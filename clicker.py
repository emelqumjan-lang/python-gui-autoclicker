"""
Автокликер с современным GUI на customtkinter.

Архитектура:
- Clicker (threading.Thread) — фоновый daemon-поток для цикла кликов.
- App (ctk.CTk) — только GUI и передача настроек в Clicker.
- keyboard.Listener — глобальный перехват горячих клавиш в отдельном потоке pynput.
"""

import json
import random
import threading
import time
from pathlib import Path
from typing import Any, Callable

import customtkinter as ctk
from pynput.keyboard import Key, KeyCode, Listener
from pynput.mouse import Button, Controller

# --- Цветовая палитра (тёмная тема с фиолетовыми акцентами) ---
COLOR_BG = "#0D0D1A"
COLOR_CARD = "#16162A"
COLOR_CARD_BORDER = "#2A2A45"
COLOR_PURPLE = "#7B2CBF"
COLOR_PURPLE_LIGHT = "#9D4EDD"
COLOR_PURPLE_GLOW = "#6A1B9A"
COLOR_TEXT = "#FFFFFF"
COLOR_TEXT_DIM = "#8B8BA8"
COLOR_GREEN = "#22C55E"
COLOR_RED = "#EF4444"

MIN_CPS = 1
MAX_CPS = 100
DEFAULT_CPS = 100
DEFAULT_RAND_PCT = 5
MIN_INTERVAL_SEC = 0.001
IDLE_SLEEP_SEC = 0.05
DOUBLE_CLICK_PAUSE_SEC = 0.05

BUTTON_MAP = {
    "Левая": Button.left,
    "Правая": Button.right,
    "Средняя": Button.middle,
}

MODE_NORMAL = "Обычный"
MODE_HOLD = "Удержание"
MODE_AREA = "По области"

CONFIG_FILE = Path(__file__).resolve().parent / "config.json"
CONFIG_VERSION = 1
SAVE_DEBOUNCE_MS = 400


def default_config() -> dict[str, Any]:
    """Настройки по умолчанию."""
    return {
        "version": CONFIG_VERSION,
        "cps": DEFAULT_CPS,
        "button": "Левая",
        "mode": MODE_NORMAL,
        "start_delay": 0.0,
        "randomization": DEFAULT_RAND_PCT,
        "click_limit": 0,
        "hotkey": {"type": "key", "name": "f6"},
        "topmost": False,
        "double_click": False,
        "total_clicks": 0,
    }


def serialize_hotkey(key) -> dict[str, Any]:
    """Сериализует клавишу pynput для JSON."""
    if isinstance(key, Key):
        return {"type": "key", "name": key.name}
    if isinstance(key, KeyCode):
        return {"type": "keycode", "char": key.char, "vk": key.vk}
    return {"type": "key", "name": "f6"}


def deserialize_hotkey(data: dict[str, Any] | None):
    """Восстанавливает клавишу pynput из JSON."""
    if not data:
        return Key.f6
    try:
        if data.get("type") == "key":
            name = str(data.get("name", "f6"))
            return getattr(Key, name, Key.f6)
        if data.get("type") == "keycode":
            char = data.get("char")
            vk = data.get("vk")
            if char:
                return KeyCode.from_char(char)
            if vk is not None:
                return KeyCode.from_vk(int(vk))
    except Exception:
        pass
    return Key.f6


def load_config_file() -> dict[str, Any]:
    """Загружает config.json или возвращает настройки по умолчанию."""
    config = default_config()
    if not CONFIG_FILE.exists():
        return config
    try:
        with CONFIG_FILE.open(encoding="utf-8") as file:
            loaded = json.load(file)
        if isinstance(loaded, dict):
            config.update(loaded)
    except (OSError, json.JSONDecodeError, TypeError):
        pass
    return config


def save_config_file(config: dict[str, Any]) -> None:
    """Сохраняет настройки в config.json."""
    try:
        with CONFIG_FILE.open("w", encoding="utf-8") as file:
            json.dump(config, file, ensure_ascii=False, indent=2)
    except OSError:
        pass


def clamp(value: float, min_value: float, max_value: float) -> float:
    """Ограничивает число заданным диапазоном."""
    return max(min_value, min(max_value, value))


def format_hotkey(key) -> str:
    """Преобразует объект клавиши pynput в читаемую строку."""
    if isinstance(key, Key):
        name = str(key).replace("Key.", "")
        return name.upper() if len(name) <= 3 else name.capitalize()
    if isinstance(key, KeyCode) and key.char:
        return key.char.upper()
    if isinstance(key, KeyCode) and key.vk:
        return f"VK{key.vk}"
    return "F6"


def keys_equal(key_a, key_b) -> bool:
    """Сравнивает две клавиши pynput с учётом Key и KeyCode."""
    if type(key_a) is not type(key_b):
        return False
    if isinstance(key_a, Key):
        return key_a == key_b
    if isinstance(key_a, KeyCode):
        if key_a.char and key_b.char:
            return key_a.char == key_b.char
        return key_a.vk == key_b.vk
    return False


def cps_to_interval(cps: float) -> float:
    """Переводит кликов в секунду в интервал между кликами."""
    return max(1.0 / max(cps, MIN_CPS), MIN_INTERVAL_SEC)


class Clicker(threading.Thread):
    """
    Фоновый поток кликов мыши.

    Daemon-поток: завершается автоматически при закрытии главного приложения.
    Флаг running — кликер включён/выключен (F6).
    Флаг program_running — приложение открыто; при False поток выходит из run().
    """

    def __init__(
        self,
        on_click: Callable[[int], None] | None = None,
        on_stop: Callable[[], None] | None = None,
    ):
        super().__init__(daemon=True)
        self.running = False
        self.program_running = True
        self.click_count = 0
        self._on_click = on_click
        self._on_stop = on_stop

        self._lock = threading.Lock()
        self._interval_sec = cps_to_interval(DEFAULT_CPS)
        self._button = Button.left
        self._double_click = False
        self._mode = MODE_NORMAL
        self._start_delay_sec = 0.0
        self._randomization_pct = 0.0
        self._click_limit = 0
        self._hold_active = False
        self._hold_button = None
        self._delay_pending = False

        self._mouse = Controller()

    def update_settings(
        self,
        interval_sec: float,
        button: Button,
        double_click: bool,
        mode: str,
        start_delay_sec: float,
        randomization_pct: float,
        click_limit: int,
    ) -> None:
        """Потокобезопасное обновление настроек без перезапуска потока."""
        with self._lock:
            self._interval_sec = max(interval_sec, MIN_INTERVAL_SEC)
            self._button = button
            self._double_click = double_click
            self._mode = mode
            self._start_delay_sec = max(0.0, start_delay_sec)
            self._randomization_pct = max(0.0, min(50.0, randomization_pct))
            self._click_limit = max(0, click_limit)

    def start_clicking(self) -> None:
        """Включает цикл кликов (с учётом задержки старта)."""
        with self._lock:
            self._delay_pending = self._start_delay_sec > 0
        self.running = True

    def stop_clicking(self) -> None:
        """Выключает цикл кликов и отпускает кнопку в режиме удержания."""
        self.running = False
        self._release_hold()

    def reset_counter(self) -> None:
        """Сбрасывает счётчик кликов."""
        self.click_count = 0

    def _release_hold(self) -> None:
        """Отпускает кнопку мыши, если активен режим удержания."""
        if self._hold_active and self._hold_button is not None:
            try:
                self._mouse.release(self._hold_button)
            except Exception:
                pass
            self._hold_active = False
            self._hold_button = None

    def _stop_internal(self) -> None:
        """Останавливает кликер и уведомляет GUI."""
        self.running = False
        self._release_hold()
        if self._on_stop:
            self._on_stop()

    def _get_settings(self) -> tuple:
        """Снимок текущих настроек под блокировкой."""
        with self._lock:
            return (
                self._interval_sec,
                self._button,
                self._double_click,
                self._mode,
                self._start_delay_sec,
                self._randomization_pct,
                self._click_limit,
                self._delay_pending,
            )

    def _clear_delay_pending(self) -> None:
        with self._lock:
            self._delay_pending = False

    def _randomized_interval(self, base_interval: float, rand_pct: float) -> float:
        """Добавляет случайное отклонение к интервалу (рандомизация)."""
        if rand_pct <= 0:
            return base_interval
        factor = 1.0 + random.uniform(-rand_pct, rand_pct) / 100.0
        return max(base_interval * factor, MIN_INTERVAL_SEC)

    def _notify_click(self) -> None:
        """Увеличивает счётчик и уведомляет GUI."""
        self.click_count += 1
        if self._on_click:
            self._on_click(self.click_count)

    def _perform_click(self, button: Button, double_click: bool) -> None:
        """Выполняет одиночный или двойной клик выбранной кнопкой мыши."""
        clicks = 2 if double_click else 1
        for i in range(clicks):
            self._mouse.press(button)
            self._mouse.release(button)
            self._notify_click()
            if double_click and i == 0:
                time.sleep(DOUBLE_CLICK_PAUSE_SEC)

    def _perform_hold(self, button: Button) -> None:
        """Зажимает кнопку мыши в режиме удержания."""
        if not self._hold_active:
            self._mouse.press(button)
            self._hold_active = True
            self._hold_button = button

    def run(self) -> None:
        """
        Основной цикл фонового потока.

        GUI-поток (mainloop) никогда не блокируется: вся работа с мышью
        и time.sleep() выполняется только здесь.
        """
        while self.program_running:
            if self.running:
                settings = self._get_settings()
                (
                    interval,
                    button,
                    double_click,
                    mode,
                    start_delay,
                    rand_pct,
                    click_limit,
                    delay_pending,
                ) = settings

                # Задержка перед первым кликом после старта.
                if delay_pending:
                    time.sleep(start_delay)
                    self._clear_delay_pending()

                if not self.running:
                    continue

                try:
                    if mode == MODE_HOLD:
                        self._perform_hold(button)
                        actual_interval = self._randomized_interval(
                            interval, rand_pct
                        )
                        time.sleep(actual_interval)
                    elif mode == MODE_AREA:
                        # Режим «по области» — клик в текущей позиции курсора.
                        self._perform_click(button, double_click)
                        actual_interval = self._randomized_interval(
                            interval, rand_pct
                        )
                        time.sleep(actual_interval)
                    else:
                        self._perform_click(button, double_click)
                        actual_interval = self._randomized_interval(
                            interval, rand_pct
                        )
                        time.sleep(actual_interval)
                except Exception:
                    self._stop_internal()

                # Остановка при достижении лимита кликов.
                if click_limit > 0 and self.click_count >= click_limit:
                    self._stop_internal()
            else:
                self._release_hold()
                time.sleep(IDLE_SLEEP_SEC)


class App(ctk.CTk):
    """Главное окно в стиле мобильного приложения с нижней навигацией."""

    def __init__(self):
        super().__init__()

        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("dark-blue")

        self.configure(fg_color=COLOR_BG)
        self.title("AutoClicker")
        self.geometry("400x700")
        self.resizable(False, False)

        self.hotkey = Key.f6
        self.capturing_hotkey = False
        self.is_clicking = False
        self.active_mode = MODE_NORMAL
        self.click_limit = 0
        self.total_clicks_all_time = 0
        self.current_page = "home"
        self.keyboard_listener = None
        self._save_job = None
        self._loading_config = False

        self.clicker = Clicker(
            on_click=self._on_click_count_changed,
            on_stop=self._on_clicker_stopped,
        )
        self.clicker.start()

        self._build_ui()
        self._load_config()
        self._start_keyboard_listener()
        self.protocol("WM_DELETE_WINDOW", self._on_closing)

    # --- Вспомогательные виджеты ---

    def _section_title(self, parent, text: str, row: int) -> None:
        """Заголовок секции (мелкий серый uppercase-стиль)."""
        ctk.CTkLabel(
            parent,
            text=text,
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color=COLOR_TEXT_DIM,
            anchor="w",
        ).grid(row=row, column=0, columnspan=2, sticky="w", pady=(4, 2))

    def _card(self, parent, **kwargs) -> ctk.CTkFrame:
        """Тёмная карточка с закруглёнными углами."""
        defaults = {
            "fg_color": COLOR_CARD,
            "border_color": COLOR_CARD_BORDER,
            "border_width": 1,
            "corner_radius": 12,
        }
        defaults.update(kwargs)
        return ctk.CTkFrame(parent, **defaults)

    def _purple_slider(self, parent, from_, to, command, default) -> ctk.CTkSlider:
        """Слайдер с фиолетовым акцентом."""
        slider = ctk.CTkSlider(
            parent,
            from_=from_,
            to=to,
            number_of_steps=int(to - from_),
            command=command,
            button_color=COLOR_PURPLE_LIGHT,
            button_hover_color=COLOR_PURPLE,
            progress_color=COLOR_PURPLE,
            fg_color="#2A2A45",
            height=10,
        )
        slider.set(default)
        return slider

    # --- Построение интерфейса ---

    def _build_ui(self) -> None:
        """Создаёт все страницы и нижнюю навигацию."""
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)

        self._build_header()

        self.content = ctk.CTkFrame(self, fg_color="transparent")
        self.content.grid(row=1, column=0, sticky="nsew", padx=12, pady=(0, 2))
        self.content.grid_columnconfigure(0, weight=1)
        self.content.grid_rowconfigure(0, weight=1)

        self.pages = {}
        self.pages["home"] = self._build_home_page()
        self.pages["stats"] = self._build_stats_page()
        self.pages["settings"] = self._build_settings_page()
        self.pages["info"] = self._build_info_page()

        self._build_navbar()
        self._show_page("home")

    def _build_header(self) -> None:
        """Верхняя панель: логотип, название, статус готовности."""
        header = ctk.CTkFrame(self, fg_color="transparent")
        header.grid(row=0, column=0, sticky="ew", padx=12, pady=(8, 4))
        header.grid_columnconfigure(1, weight=1)

        logo = ctk.CTkFrame(
            header,
            width=34,
            height=34,
            corner_radius=17,
            fg_color=COLOR_PURPLE,
        )
        logo.grid(row=0, column=0, padx=(0, 8))
        logo.grid_propagate(False)
        ctk.CTkLabel(
            logo,
            text="➤",
            font=ctk.CTkFont(size=14, weight="bold"),
            text_color=COLOR_TEXT,
        ).place(relx=0.5, rely=0.5, anchor="center")

        title_block = ctk.CTkFrame(header, fg_color="transparent")
        title_block.grid(row=0, column=1, sticky="w")
        ctk.CTkLabel(
            title_block,
            text="AutoClicker",
            font=ctk.CTkFont(size=18, weight="bold"),
            text_color=COLOR_TEXT,
            anchor="w",
        ).pack(anchor="w")
        ctk.CTkLabel(
            title_block,
            text="Быстрые клики. Максимум эффективности.",
            font=ctk.CTkFont(size=9),
            text_color=COLOR_TEXT_DIM,
            anchor="w",
        ).pack(anchor="w")

        self.ready_label = ctk.CTkLabel(
            header,
            text="● Готов к работе",
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color=COLOR_GREEN,
        )
        self.ready_label.grid(row=0, column=2, sticky="e")

    def _build_home_page(self) -> ctk.CTkFrame:
        """Главная страница — статус, настройки, режимы, хоткеи."""
        page = ctk.CTkFrame(self.content, fg_color="transparent")
        page.grid_columnconfigure(0, weight=1)

        # --- Карточка статуса (горизонтальная — экономит высоту) ---
        status_card = self._card(
            page,
            border_color=COLOR_PURPLE,
            border_width=2,
        )
        status_card.grid(row=0, column=0, sticky="ew", pady=(0, 4))
        status_card.grid_columnconfigure(0, weight=1)

        status_left = ctk.CTkFrame(status_card, fg_color="transparent")
        status_left.grid(row=0, column=0, rowspan=2, padx=(12, 4), pady=10, sticky="nw")

        ctk.CTkLabel(
            status_left,
            text="СТАТУС",
            font=ctk.CTkFont(size=9, weight="bold"),
            text_color=COLOR_TEXT_DIM,
        ).pack(anchor="w")

        self.status_big_label = ctk.CTkLabel(
            status_left,
            text="ВЫКЛ  ⏻",
            font=ctk.CTkFont(size=24, weight="bold"),
            text_color=COLOR_PURPLE_LIGHT,
        )
        self.status_big_label.pack(anchor="w", pady=(0, 0))

        self.clicks_label = ctk.CTkLabel(
            status_left,
            text="клики: 0",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_TEXT_DIM,
        )
        self.clicks_label.pack(anchor="w")

        self.status_hint_label = ctk.CTkLabel(
            status_left,
            text="Нажмите, чтобы запустить",
            font=ctk.CTkFont(size=10),
            text_color=COLOR_TEXT_DIM,
        )
        self.status_hint_label.pack(anchor="w", pady=(2, 0))

        self.main_toggle_btn = ctk.CTkButton(
            status_card,
            text="🖱",
            width=76,
            height=76,
            corner_radius=38,
            font=ctk.CTkFont(size=28),
            fg_color=COLOR_PURPLE,
            hover_color=COLOR_PURPLE_GLOW,
            border_width=2,
            border_color=COLOR_PURPLE_LIGHT,
            command=self.toggle_clicking,
        )
        self.main_toggle_btn.grid(row=0, column=1, rowspan=2, padx=(0, 12), pady=10)

        # --- Основные настройки ---
        self._section_title(page, "ОСНОВНЫЕ НАСТРОЙКИ", 1)

        settings_row = ctk.CTkFrame(page, fg_color="transparent")
        settings_row.grid(row=2, column=0, sticky="ew", pady=(0, 2))
        settings_row.grid_columnconfigure(0, weight=1)
        settings_row.grid_columnconfigure(1, weight=1)

        speed_card = self._card(settings_row)
        speed_card.grid(row=0, column=0, sticky="nsew", padx=(0, 5))
        speed_card.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            speed_card,
            text="⚡ СКОРОСТЬ КЛИКОВ",
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color=COLOR_TEXT_DIM,
        ).grid(row=0, column=0, padx=8, pady=(6, 2), sticky="w")

        self.cps_value_label = ctk.CTkLabel(
            speed_card,
            text=f"{DEFAULT_CPS} кликов/сек",
            font=ctk.CTkFont(size=14, weight="bold"),
            text_color=COLOR_TEXT,
        )
        self.cps_value_label.grid(row=1, column=0, padx=8, sticky="w")

        self.cps_slider = self._purple_slider(
            speed_card, MIN_CPS, MAX_CPS, self._on_cps_changed, DEFAULT_CPS
        )
        self.cps_slider.grid(row=2, column=0, padx=8, pady=(2, 8), sticky="ew")

        button_card = self._card(settings_row)
        button_card.grid(row=0, column=1, sticky="nsew", padx=(5, 0))
        button_card.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            button_card,
            text="🖱 КНОПКА",
            font=ctk.CTkFont(size=10, weight="bold"),
            text_color=COLOR_TEXT_DIM,
        ).grid(row=0, column=0, padx=8, pady=(6, 2), sticky="w")

        self.button_combo = ctk.CTkComboBox(
            button_card,
            values=list(BUTTON_MAP.keys()),
            state="readonly",
            height=28,
            font=ctk.CTkFont(size=12),
            fg_color="#1E1E35",
            border_color=COLOR_CARD_BORDER,
            button_color=COLOR_PURPLE,
            button_hover_color=COLOR_PURPLE_GLOW,
            dropdown_fg_color=COLOR_CARD,
            command=self._on_button_changed,
        )
        self.button_combo.set("Левая")
        self.button_combo.grid(row=1, column=0, padx=8, pady=(2, 2), sticky="ew")

        self.mouse_hint_label = ctk.CTkLabel(
            button_card,
            text="Мышь: Левая",
            font=ctk.CTkFont(size=9),
            text_color=COLOR_TEXT_DIM,
        )
        self.mouse_hint_label.grid(row=2, column=0, padx=8, pady=(0, 8), sticky="w")

        # --- Режимы ---
        self._section_title(page, "РЕЖИМЫ", 3)

        modes_frame = ctk.CTkFrame(page, fg_color="transparent")
        modes_frame.grid(row=4, column=0, sticky="ew", pady=(0, 2))
        modes_frame.grid_columnconfigure((0, 1, 2), weight=1)

        self.mode_buttons = {}
        modes = [
            (MODE_NORMAL, "◎ Обычный"),
            (MODE_HOLD, "▣ Удержание"),
            (MODE_AREA, "✦ По области"),
        ]
        for col, (mode_id, label) in enumerate(modes):
            btn = ctk.CTkButton(
                modes_frame,
                text=label,
                height=28,
                corner_radius=14,
                font=ctk.CTkFont(size=10),
                fg_color="transparent",
                border_width=1,
                border_color=COLOR_CARD_BORDER,
                hover_color="#252540",
                command=lambda m=mode_id: self._set_mode(m),
            )
            btn.grid(row=0, column=col, padx=3, sticky="ew")
            self.mode_buttons[mode_id] = btn

        self._set_mode(MODE_NORMAL)

        # --- Дополнительные настройки ---
        self._section_title(page, "ДОП. НАСТРОЙКИ", 5)

        extra_row = ctk.CTkFrame(page, fg_color="transparent")
        extra_row.grid(row=6, column=0, sticky="ew", pady=(0, 2))
        extra_row.grid_columnconfigure((0, 1, 2), weight=1)

        delay_card = self._card(extra_row)
        delay_card.grid(row=0, column=0, sticky="nsew", padx=(0, 4))
        delay_card.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            delay_card,
            text="🕐 ЗАДЕРЖКА СТАРТА",
            font=ctk.CTkFont(size=9, weight="bold"),
            text_color=COLOR_TEXT_DIM,
        ).grid(row=0, column=0, padx=6, pady=(6, 0), sticky="w")

        self.delay_label = ctk.CTkLabel(
            delay_card,
            text="0.0 сек",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color=COLOR_TEXT,
        )
        self.delay_label.grid(row=1, column=0, padx=6, sticky="w")

        self.delay_slider = self._purple_slider(
            delay_card, 0, 50, self._on_delay_changed, 0
        )
        self.delay_slider.grid(row=2, column=0, padx=6, pady=(2, 6), sticky="ew")

        rand_card = self._card(extra_row)
        rand_card.grid(row=0, column=1, sticky="nsew", padx=2)
        rand_card.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            rand_card,
            text="⊞ РАНДОМИЗАЦИЯ",
            font=ctk.CTkFont(size=9, weight="bold"),
            text_color=COLOR_TEXT_DIM,
        ).grid(row=0, column=0, padx=6, pady=(6, 0), sticky="w")

        self.rand_label = ctk.CTkLabel(
            rand_card,
            text="0 %",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color=COLOR_TEXT,
        )
        self.rand_label.grid(row=1, column=0, padx=6, sticky="w")

        self.rand_slider = self._purple_slider(
            rand_card, 0, 50, self._on_rand_changed, DEFAULT_RAND_PCT
        )
        self.rand_label.configure(text=f"{DEFAULT_RAND_PCT} %")
        self.rand_slider.grid(row=2, column=0, padx=6, pady=(2, 6), sticky="ew")

        limit_card = self._card(extra_row)
        limit_card.grid(row=0, column=2, sticky="nsew", padx=(4, 0))
        limit_card.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            limit_card,
            text="☑ ОГРАНИЧЕНИЕ",
            font=ctk.CTkFont(size=9, weight="bold"),
            text_color=COLOR_TEXT_DIM,
        ).grid(row=0, column=0, padx=6, pady=(6, 0), sticky="w")

        self.limit_label = ctk.CTkLabel(
            limit_card,
            text="Без лимита",
            font=ctk.CTkFont(size=11, weight="bold"),
            text_color=COLOR_TEXT,
        )
        self.limit_label.grid(row=1, column=0, padx=6, sticky="w")

        ctk.CTkButton(
            limit_card,
            text="Установить",
            height=22,
            font=ctk.CTkFont(size=10),
            fg_color="transparent",
            border_width=1,
            border_color=COLOR_TEXT_DIM,
            hover_color="#252540",
            command=self._set_click_limit,
        ).grid(row=2, column=0, padx=6, pady=(2, 6), sticky="ew")

        # --- Горячие клавиши ---
        hotkey_card = self._card(page)
        hotkey_card.grid(row=7, column=0, sticky="ew", pady=(2, 4))
        hotkey_card.grid_columnconfigure(2, weight=1)

        ctk.CTkLabel(
            hotkey_card,
            text="ГОРЯЧИЕ КЛАВИШИ",
            font=ctk.CTkFont(size=9, weight="bold"),
            text_color=COLOR_TEXT_DIM,
        ).grid(row=0, column=0, columnspan=4, padx=10, pady=(6, 2), sticky="w")

        self.hotkey_box = ctk.CTkButton(
            hotkey_card,
            text=format_hotkey(self.hotkey),
            width=52,
            height=28,
            font=ctk.CTkFont(size=12, weight="bold"),
            fg_color="#1E1E35",
            hover_color="#252540",
            border_width=1,
            border_color=COLOR_CARD_BORDER,
            command=self._start_hotkey_capture,
        )
        self.hotkey_box.grid(row=1, column=0, padx=(10, 4), pady=(0, 8))

        ctk.CTkLabel(
            hotkey_card,
            text="✎",
            font=ctk.CTkFont(size=13),
            text_color=COLOR_TEXT_DIM,
        ).grid(row=1, column=1, sticky="w", pady=(0, 8))

        ctk.CTkLabel(
            hotkey_card,
            text="Запуск / Остановка",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_TEXT,
        ).grid(row=1, column=2, padx=8, pady=(0, 8), sticky="e")

        return page

    def _build_stats_page(self) -> ctk.CTkFrame:
        """Страница статистики."""
        page = ctk.CTkFrame(self.content, fg_color="transparent")
        page.grid_columnconfigure(0, weight=1)

        card = self._card(page)
        card.grid(row=0, column=0, sticky="ew", pady=10)
        card.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            card,
            text="СТАТИСТИКА",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color=COLOR_TEXT_DIM,
        ).grid(row=0, column=0, padx=16, pady=(16, 8), sticky="w")

        self.stats_session_label = ctk.CTkLabel(
            card,
            text="Кликов в сессии: 0",
            font=ctk.CTkFont(size=16),
            text_color=COLOR_TEXT,
            anchor="w",
        )
        self.stats_session_label.grid(row=1, column=0, padx=16, pady=6, sticky="ew")

        self.stats_total_label = ctk.CTkLabel(
            card,
            text="Всего кликов: 0",
            font=ctk.CTkFont(size=16),
            text_color=COLOR_TEXT,
            anchor="w",
        )
        self.stats_total_label.grid(row=2, column=0, padx=16, pady=6, sticky="ew")

        self.stats_cps_label = ctk.CTkLabel(
            card,
            text=f"Скорость: {DEFAULT_CPS} кликов/сек",
            font=ctk.CTkFont(size=16),
            text_color=COLOR_TEXT,
            anchor="w",
        )
        self.stats_cps_label.grid(row=3, column=0, padx=16, pady=6, sticky="ew")

        ctk.CTkButton(
            card,
            text="Сбросить счётчик",
            fg_color=COLOR_PURPLE,
            hover_color=COLOR_PURPLE_GLOW,
            command=self._reset_stats,
        ).grid(row=4, column=0, padx=16, pady=(12, 16), sticky="ew")

        return page

    def _build_settings_page(self) -> ctk.CTkFrame:
        """Страница настроек."""
        page = ctk.CTkFrame(self.content, fg_color="transparent")
        page.grid_columnconfigure(0, weight=1)

        card = self._card(page)
        card.grid(row=0, column=0, sticky="ew", pady=10)
        card.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            card,
            text="НАСТРОЙКИ",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color=COLOR_TEXT_DIM,
        ).grid(row=0, column=0, padx=16, pady=(16, 8), sticky="w")

        self.topmost_var = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(
            card,
            text="Поверх всех окон (Topmost)",
            variable=self.topmost_var,
            command=self._toggle_topmost,
            fg_color=COLOR_PURPLE,
            hover_color=COLOR_PURPLE_GLOW,
        ).grid(row=1, column=0, padx=16, pady=8, sticky="w")

        self.double_click_var = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(
            card,
            text="Двойной клик",
            variable=self.double_click_var,
            command=self._schedule_save,
            fg_color=COLOR_PURPLE,
            hover_color=COLOR_PURPLE_GLOW,
        ).grid(row=2, column=0, padx=16, pady=8, sticky="w")

        return page

    def _build_info_page(self) -> ctk.CTkFrame:
        """Страница информации о приложении."""
        page = ctk.CTkFrame(self.content, fg_color="transparent")
        page.grid_columnconfigure(0, weight=1)

        card = self._card(page, border_color=COLOR_PURPLE, border_width=1)
        card.grid(row=0, column=0, sticky="ew", pady=10)
        card.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            card,
            text="AutoClicker v1.0",
            font=ctk.CTkFont(size=20, weight="bold"),
            text_color=COLOR_PURPLE_LIGHT,
        ).grid(row=0, column=0, padx=16, pady=(20, 8))

        info_text = (
            "Автокликер с глобальными горячими клавишами.\n\n"
            "• F6 — запуск / остановка\n"
            "• Настройки сохраняются в config.json\n"
            "• Работает в фоновом потоке\n"
            "• Не блокирует интерфейс\n\n"
            "Стек: customtkinter + pynput"
        )
        ctk.CTkLabel(
            card,
            text=info_text,
            font=ctk.CTkFont(size=13),
            text_color=COLOR_TEXT_DIM,
            justify="left",
            anchor="w",
        ).grid(row=1, column=0, padx=16, pady=(0, 20), sticky="w")

        return page

    def _build_navbar(self) -> None:
        """Нижняя панель навигации."""
        nav = ctk.CTkFrame(
            self,
            fg_color=COLOR_CARD,
            corner_radius=0,
            height=48,
            border_width=1,
            border_color=COLOR_CARD_BORDER,
        )
        nav.grid(row=2, column=0, sticky="ew")
        nav.grid_columnconfigure((0, 1, 2, 3), weight=1)

        self.nav_buttons = {}
        nav_items = [
            ("home", "⌂", "Главная"),
            ("stats", "◷", "Статистика"),
            ("settings", "⚙", "Настройки"),
            ("info", "ℹ", "Инфо"),
        ]
        for col, (page_id, icon, label) in enumerate(nav_items):
            btn = ctk.CTkButton(
                nav,
                text=f"{icon}\n{label}",
                height=44,
                font=ctk.CTkFont(size=9),
                fg_color="transparent",
                hover_color="#252540",
                text_color=COLOR_TEXT_DIM,
                command=lambda p=page_id: self._show_page(p),
            )
            btn.grid(row=0, column=col, sticky="nsew")
            self.nav_buttons[page_id] = btn

    def _show_page(self, page_id: str) -> None:
        """Переключает видимую страницу и подсвечивает вкладку навигации."""
        for pid, frame in self.pages.items():
            if pid == page_id:
                frame.grid(row=0, column=0, sticky="nsew")
            else:
                frame.grid_forget()

        self.current_page = page_id
        for pid, btn in self.nav_buttons.items():
            if pid == page_id:
                btn.configure(text_color=COLOR_PURPLE_LIGHT)
            else:
                btn.configure(text_color=COLOR_TEXT_DIM)

    # --- Сохранение и загрузка настроек ---

    def _collect_config(self) -> dict[str, Any]:
        """Собирает текущие настройки приложения в словарь."""
        cps = int(clamp(self.cps_slider.get(), MIN_CPS, MAX_CPS))
        delay = round(clamp(self.delay_slider.get(), 0, 50) / 10, 1)
        rand_pct = int(clamp(self.rand_slider.get(), 0, 50))
        button = self.button_combo.get()
        if button not in BUTTON_MAP:
            button = "Левая"
        mode = self.active_mode
        if mode not in {MODE_NORMAL, MODE_HOLD, MODE_AREA}:
            mode = MODE_NORMAL
        return {
            "version": CONFIG_VERSION,
            "cps": cps,
            "button": button,
            "mode": mode,
            "start_delay": delay,
            "randomization": rand_pct,
            "click_limit": max(0, int(self.click_limit)),
            "hotkey": serialize_hotkey(self.hotkey),
            "topmost": bool(self.topmost_var.get()),
            "double_click": bool(self.double_click_var.get()),
            "total_clicks": max(0, int(self.total_clicks_all_time)),
        }

    def _apply_config(self, config: dict[str, Any]) -> None:
        """Применяет загруженные настройки к интерфейсу."""
        cps = int(clamp(config.get("cps", DEFAULT_CPS), MIN_CPS, MAX_CPS))
        button = config.get("button", "Левая")
        if button not in BUTTON_MAP:
            button = "Левая"
        mode = config.get("mode", MODE_NORMAL)
        if mode not in {MODE_NORMAL, MODE_HOLD, MODE_AREA}:
            mode = MODE_NORMAL
        delay = round(clamp(float(config.get("start_delay", 0.0)), 0.0, 5.0), 1)
        rand_pct = int(clamp(float(config.get("randomization", DEFAULT_RAND_PCT)), 0, 50))
        click_limit = max(0, int(config.get("click_limit", 0)))
        self.total_clicks_all_time = max(0, int(config.get("total_clicks", 0)))

        self.cps_slider.set(cps)
        self._on_cps_changed(cps)

        self.button_combo.set(button)
        self._on_button_changed(button)

        self.delay_slider.set(delay * 10)
        self._on_delay_changed(delay * 10)

        self.rand_slider.set(rand_pct)
        self._on_rand_changed(rand_pct)

        self.click_limit = click_limit
        if click_limit == 0:
            self.limit_label.configure(text="Без лимита")
        else:
            self.limit_label.configure(text=f"Лимит: {click_limit}")

        self._set_mode(mode)

        self.hotkey = deserialize_hotkey(config.get("hotkey"))
        self.hotkey_box.configure(text=format_hotkey(self.hotkey))

        self.topmost_var.set(bool(config.get("topmost", False)))
        self._toggle_topmost()

        self.double_click_var.set(bool(config.get("double_click", False)))

        self.stats_total_label.configure(
            text=f"Всего кликов: {self.total_clicks_all_time}"
        )

    def _load_config(self) -> None:
        """Загружает настройки из config.json при запуске."""
        self._loading_config = True
        try:
            self._apply_config(load_config_file())
        finally:
            self._loading_config = False

    def _save_config(self) -> None:
        """Сохраняет текущие настройки в config.json."""
        self._save_job = None
        save_config_file(self._collect_config())

    def _schedule_save(self, *_args) -> None:
        """Откладывает сохранение, чтобы не писать файл на каждый пиксель слайдера."""
        if self._loading_config:
            return
        if self._save_job is not None:
            self.after_cancel(self._save_job)
        self._save_job = self.after(SAVE_DEBOUNCE_MS, self._save_config)

    # --- Обработчики настроек ---

    def _on_cps_changed(self, value: float) -> None:
        """Обновляет отображение скорости кликов."""
        cps = int(value)
        self.cps_value_label.configure(text=f"{cps} кликов/сек")
        self.stats_cps_label.configure(text=f"Скорость: {cps} кликов/сек")
        self._schedule_save()

    def _on_button_changed(self, value: str) -> None:
        """Обновляет подпись выбранной кнопки мыши."""
        self.mouse_hint_label.configure(text=f"Мышь: {value}")
        self._schedule_save()

    def _on_delay_changed(self, value: float) -> None:
        """Обновляет задержку старта (слайдер 0–5.0 сек)."""
        delay = round(value / 10, 1)
        self.delay_label.configure(text=f"{delay} сек")
        self._schedule_save()

    def _on_rand_changed(self, value: float) -> None:
        """Обновляет процент рандомизации интервала."""
        pct = int(value)
        self.rand_label.configure(text=f"{pct} %")
        self._schedule_save()

    def _set_mode(self, mode: str) -> None:
        """Переключает режим кликов и подсвечивает активную кнопку."""
        self.active_mode = mode
        for mode_id, btn in self.mode_buttons.items():
            if mode_id == mode:
                btn.configure(
                    fg_color=COLOR_PURPLE,
                    border_color=COLOR_PURPLE_LIGHT,
                    text_color=COLOR_TEXT,
                )
            else:
                btn.configure(
                    fg_color="transparent",
                    border_color=COLOR_CARD_BORDER,
                    text_color=COLOR_TEXT_DIM,
                )
        self._schedule_save()

    def _set_click_limit(self) -> None:
        """Диалог установки лимита кликов."""
        dialog = ctk.CTkInputDialog(
            text="Введите лимит кликов (0 = без лимита):",
            title="Ограничение",
        )
        result = dialog.get_input()
        if result is None:
            return
        try:
            limit = int(result.strip())
            if limit < 0:
                raise ValueError
            self.click_limit = limit
            if limit == 0:
                self.limit_label.configure(text="Без лимита")
            else:
                self.limit_label.configure(text=f"Лимит: {limit}")
        except ValueError:
            self.limit_label.configure(text="Ошибка ввода")
        else:
            self._schedule_save()

    def _get_settings_from_ui(self) -> dict:
        """Собирает все настройки из виджетов."""
        cps = int(self.cps_slider.get())
        delay = round(self.delay_slider.get() / 10, 1)
        rand_pct = int(self.rand_slider.get())
        return {
            "interval": cps_to_interval(cps),
            "button": BUTTON_MAP[self.button_combo.get()],
            "double_click": self.double_click_var.get(),
            "mode": self.active_mode,
            "start_delay": delay,
            "randomization": rand_pct,
            "click_limit": self.click_limit,
        }

    def _toggle_topmost(self) -> None:
        """Включает/выключает режим «поверх всех окон»."""
        self.attributes("-topmost", self.topmost_var.get())
        self._schedule_save()

    def _on_click_count_changed(self, count: int) -> None:
        """
        Callback из потока Clicker — обновляет счётчики в GUI-потоке.

        Нельзя менять виджеты напрямую из фонового потока.
        """
        self.after(0, lambda c=count: self._update_click_labels(c))

    def _on_clicker_stopped(self) -> None:
        """Callback при автоматической остановке кликера (лимит / ошибка)."""
        self.after(0, self._sync_stopped_state)

    def _sync_stopped_state(self) -> None:
        """Синхронизирует UI после остановки фонового потока."""
        if self.is_clicking:
            self.is_clicking = False
            self._update_status_ui()

    def _update_click_labels(self, count: int) -> None:
        """Обновляет все метки со счётчиком кликов."""
        self.total_clicks_all_time += 1
        self.clicks_label.configure(text=f"клики: {count}")
        self.stats_session_label.configure(text=f"Кликов в сессии: {count}")
        self.stats_total_label.configure(
            text=f"Всего кликов: {self.total_clicks_all_time}"
        )
        if count % 10 == 0:
            self._schedule_save()

    def _reset_stats(self) -> None:
        """Сбрасывает счётчики кликов."""
        self.clicker.reset_counter()
        self.clicks_label.configure(text="клики: 0")
        self.stats_session_label.configure(text="Кликов в сессии: 0")

    def _update_status_ui(self) -> None:
        """Обновляет индикаторы статуса на главной странице."""
        if self.is_clicking:
            self.status_big_label.configure(text="ВКЛ  ⏻", text_color=COLOR_GREEN)
            self.status_hint_label.configure(text="Нажмите, чтобы остановить")
            self.ready_label.configure(
                text="● Работает",
                text_color=COLOR_GREEN,
            )
            self.main_toggle_btn.configure(
                fg_color=COLOR_PURPLE_GLOW,
                border_color=COLOR_GREEN,
            )
        else:
            self.status_big_label.configure(text="ВЫКЛ  ⏻", text_color=COLOR_PURPLE_LIGHT)
            self.status_hint_label.configure(text="Нажмите, чтобы запустить")
            self.ready_label.configure(
                text="● Готов к работе",
                text_color=COLOR_GREEN,
            )
            self.main_toggle_btn.configure(
                fg_color=COLOR_PURPLE,
                border_color=COLOR_PURPLE_LIGHT,
            )

    def toggle_clicking(self) -> None:
        """
        Переключает кликер вкл/выкл.

        Вызывается из GUI-кнопки или через after() из потока keyboard.Listener.
        """
        if self.is_clicking:
            self.clicker.stop_clicking()
            self.is_clicking = False
        else:
            settings = self._get_settings_from_ui()
            # Новая сессия — сбрасываем счётчик, чтобы лимит работал корректно.
            self.clicker.reset_counter()
            self.clicks_label.configure(text="клики: 0")
            self.stats_session_label.configure(text="Кликов в сессии: 0")
            self.clicker.update_settings(
                interval_sec=settings["interval"],
                button=settings["button"],
                double_click=settings["double_click"],
                mode=settings["mode"],
                start_delay_sec=settings["start_delay"],
                randomization_pct=settings["randomization"],
                click_limit=settings["click_limit"],
            )
            self.clicker.start_clicking()
            self.is_clicking = True

        self._update_status_ui()

    def _start_hotkey_capture(self) -> None:
        """Включает режим захвата новой горячей клавиши."""
        self.capturing_hotkey = True
        self.hotkey_box.configure(
            text="...",
            border_color=COLOR_PURPLE_LIGHT,
        )

    def _finish_hotkey_capture(self, key) -> None:
        """Сохраняет новую горячую клавишу и обновляет UI (только из GUI-потока)."""
        self.hotkey = key
        self.capturing_hotkey = False
        self.hotkey_box.configure(
            text=format_hotkey(key),
            border_color=COLOR_CARD_BORDER,
        )
        self._schedule_save()

    def _on_hotkey_press(self, key) -> None:
        """
        Обработчик нажатий клавиш в фоновом потоке pynput.

        Нельзя напрямую менять виджеты tkinter из этого потока —
        используем self.after(0, ...) для безопасной передачи в GUI-поток.
        """
        if self.capturing_hotkey:
            self.after(0, lambda k=key: self._finish_hotkey_capture(k))
            return False

        if keys_equal(key, self.hotkey):
            self.after(0, self.toggle_clicking)

    def _start_keyboard_listener(self) -> None:
        """Запускает глобальный слушатель клавиш (работает при свёрнутом окне)."""
        self.keyboard_listener = Listener(on_press=self._on_hotkey_press)
        self.keyboard_listener.start()

    def _on_closing(self) -> None:
        """
        Корректное завершение приложения.

        Сбрасываем program_running — поток Clicker выходит из run().
        Останавливаем keyboard.Listener и закрываем окно.
        """
        if self._save_job is not None:
            self.after_cancel(self._save_job)
        self._save_config()

        self.clicker.program_running = False
        self.clicker.stop_clicking()
        if self.keyboard_listener:
            self.keyboard_listener.stop()
        self.destroy()


if __name__ == "__main__":
    app = App()
    app.mainloop()