# -*- coding: utf-8 -*-
"""
GUI-скрипт для вставки подписей в PDF-документ.

Требования:
    pip install PyMuPDF

Запуск:
    python pdf_signature_gui.py

Описание:
    1. Пользователь выбирает PDF-файл, список страниц (формат "1,10-16,21"
       или пусто = все страницы), папку с PNG-подписями Подписанта 1 и
       папку с PNG-подписями Подписанта 2.
    2. Режим автоопределения (по умолчанию): на каждой странице через
       page.search_for() ищутся фамилии из штампа (см. SIGNER_BY_SURNAME:
       "Чемыхин" -> Подписант 1, "Лисицын" -> Подписант 2). Каждое вхождение
       фильтруется: подпись ставится ТОЛЬКО рядом с фамилией внутри
       ГОСТ-штампа (правый нижний угол листа, попадание в таблицу
       page.find_tables() либо соседство со словами "Разработал",
       "Проверил", "ГИП", "Н.контр.", "Разраб"). Картинка размещается
       справа от фамилии в той же строке. Упоминания фамилий в основном
       тексте документа игнорируются. После выбора PDF запускается
       автоопределение, найденные позиции выводятся в журнал.
    3. Ручной режим (fallback, чекбокс «Ручной режим»): 4 подписи вставляются
       по фиксированным отступам страницы (см. SIGNATURE_SLOTS).
    4. Обработанный PDF сохраняется обратно в исходный файл
       (без создания резервных копий).
"""

import os
import re
import random
import glob
import logging
from typing import Optional

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

try:
    import pymupdf as fitz  # PyMuPDF (современное имя модуля)
except ImportError:
    import fitz  # PyMuPDF (старое имя модуля, PyMuPDF < 1.24)


# ============================================================================
# ВСЕ НАСТРАИВАЕМЫЕ ПАРАМЕТРЫ (КОНСТАНТЫ)
# ============================================================================

# Настройка модуля логирования (все этапы поиска штампа пишутся в лог)
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
)
logger = logging.getLogger("pdf_signature_gui")

# Конвертация единиц: 1 миллиметр = 2.83465 пунктов (points)
MM_TO_PT = 2.83465

# Размер подписи в миллиметрах
SIGNATURE_WIDTH_MM = 8      # ширина подписи, мм
SIGNATURE_HEIGHT_MM = 16    # высота подписи, мм

# Размер подписи в пунктах (рассчитывается из мм через MM_TO_PT)
SIGNATURE_WIDTH_PT = SIGNATURE_WIDTH_MM * MM_TO_PT     # ≈ 22.68 pt
SIGNATURE_HEIGHT_PT = SIGNATURE_HEIGHT_MM * MM_TO_PT   # ≈ 45.35 pt

# ---------------------------------------------------------------------------
# МАППИНГ «ФАМИЛИЯ -> ПОДПИСАНТ» (ключевые слова поиска вхождений фамилий)
# signer_id = 1 -> PNG из папки Подписанта 1, 2 -> папка Подписанта 2.
# Фамилии ищутся на странице через page.search_for(); подпись ставится
# справа от каждой фамилии, найденной ВНУТРИ ГОСТ-штампа.
# ---------------------------------------------------------------------------
SIGNER_BY_SURNAME: dict[str, int] = {
    "Чемыхин": 1,   # -> signer1_pngs
    "Лисицын": 2,   # -> signer2_pngs
}

# ---------------------------------------------------------------------------
# ФИЛЬТР «Фамилия внутри штампа»: отличает ГОСТ-штамп (правый нижний угол)
# от упоминаний фамилий в основном тексте документа.
# ---------------------------------------------------------------------------
# Смещение картинки подписи вправо от ПРАВОЙ ГРАНИЦЫ ЯЧЕЙКИ штампа
# (а не от текста фамилии), пунктов. Используется только как резерв,
# когда сетка ячеек не распознана; при распознавании сетки подпись
# центрируется в целевой ячейке (колонка «Подпись»).
OFFSET_RIGHT_PT = 3.0

# Минимальный зазор между текстом фамилии и левым краем подписи, пунктов.
# Используется, если правее ячейки с фамилией других квадратиков нет —
# тогда подпись ставится сразу после текста с этим отступом.
NAME_GAP_MIN_PT = 8.0

# Целевой зазор между ПРАВЫМ КРАЕМ ТЕКСТА фамилии и левым краем подписи, мм.
# Требуемое поведение: подпись появляется в SIGNATURE_GAP_FROM_NAME_MM
# миллиметрах справа от фамилии. Это главный (приоритетный) критерий
# горизонтального позиционирования; центрирование в ячейке «Подпись»
# допускается только если оно не уводит подпись дальше MAX_SIG_CELL_DEV_MM
# мм от этой точки (иначе ячейка распознана неверно/охватывает несколько
# колонок — её геометрия игнорируется).
SIGNATURE_GAP_FROM_NAME_MM = 5.0
SIGNATURE_GAP_FROM_NAME_PT = SIGNATURE_GAP_FROM_NAME_MM * MM_TO_PT  # ≈14.17 pt

# Максимальное допустимое отклонение от точки «фамилия + 5 мм» при
# использовании центрирования по ячейке, мм.
MAX_SIG_CELL_DEV_MM = 3.0
MAX_SIG_CELL_DEV_PT = MAX_SIG_CELL_DEV_MM * MM_TO_PT  # ≈8.50 pt

# Горизонтальное пересечение соседних строк текста, при котором они
# считаются ЧАСТЬЮ ОДНОЙ ячейки (строка «И.О. Фамилия» может печататься
# двумя строками; без этого критерия один текст мог бы слиться с другим).
LINE_MERGE_X_OVERLAP_RATIO = 0.5

# Максимальный вертикальный зазор между строками одной ячейки, пунктов
MAX_LINE_GAP_PT = 12.0

# Нижняя зона страницы: вхождение фамилии должно быть НЕ ВЫШЕ этой доли
# высоты страницы (штамп ГОСТ всегда в нижней части листа).
STAMP_ZONE_BOTTOM_RATIO = 0.60   # rect.y0 >= 0.60 * page_height - допуск

# Правая зона страницы: фамилия должна быть правее этой доли ширины
# страницы. Штамп может начинаться левее 40% листа — например, строка
# «Разработал | Чемыхин»: ячейка с ролью занимает ~25% ширины штампа,
# поэтому фамилия во второй колонке вполне может находиться левее 0.40 W.
STAMP_ZONE_RIGHT_RATIO = 0.20    # rect.x0 >= 0.20 * page_width - допуск

# Допуск (в пунктах) к границам зон при проверке is_rect_in_stamp():
# снимает пограничные случаи из-за неточного распознавания координат.
STAMP_ZONE_TOLERANCE_PT = 10.0

# Основной критерий: попадание центра Rect фамилии в bounding box хотя бы
# одной таблицы, найденной page.find_tables() (PyMuPDF >= 1.23).

# Fallback-критерий (если find_tables недоступен или ничего не нашёл):
# рядом с фамилией (по X ±NEIGHBOR_RADIUS_X_PT, по Y ±NEIGHBOR_RADIUS_Y_PT)
# присутствует хотя бы одно из слов-ориентиров ячеек ГОСТ-штампа.
STAMP_NEIGHBOR_WORDS: tuple[str, ...] = (
    "Разработал", "Проверил", "ГИП", "Н.контр.", "Разраб",
    # Варианты написания на чертежах (для fallback-проверки соседства):
    "Разраб.", "Гл.констр.", "Н. контр.",
    # Роли нестандартных штампов (Сбой 4: штамп без типовых заголовков):
    "Изм. внес", "Изм.внес", "Внес", "Составил", "Состав.",
    "Утв.", "Утвердил", "Согласовал", "Соглас.",
    "Главный инженер", "Гл.инж.", "Автор", "Авт.",
)

# Регулярка даты штампа формата «XX.XX» или «XX.XX.XXXX» (например,
# «03.26» или «03.26.2025») — используется эвристикой поиска колонки
# «Подпись» «колонка слева от даты» (_find_sig_column_by_date).
DATE_CELL_PATTERN = re.compile(r"^\d{2}\.\d{2}(\.\d{2,4})?$")

# Типичная ширина колонки «Дата», мм — используется третьим fallback'ом
# («предпоследняя колонка таблицы»): правая граница таблицы минус ширина
# колонки даты даёт границы колонки «Подпись».
DATE_COLUMN_TYPICAL_WIDTH_MM = 40.0
DATE_COLUMN_MIN_WIDTH_MM = 30.0
DATE_COLUMN_MAX_WIDTH_MM = 50.0
NEIGHBOR_RADIUS_X_PT = 50.0
NEIGHBOR_RADIUS_Y_PT = 30.0

# Заголовок колонки штампа, в которую ставится подпись. Колонка ищется
# по тексту заголовка в шапке таблицы (_find_signature_column_x) — это
# надёжнее, чем «ближайшая линия сетки справа от фамилии»: фамилия может
# находиться в ОБЪЕДИНЁННОЙ ячейке (охватывает колонки «Лист» и «№ док.»),
# и ближайшая внутренняя линия оказывается НЕ границей колонки «Подпись».
SIGNATURE_COLUMN_HEADER = "Подпись"
# Варианты заголовка, если точное слово не найдено (сокращения на чертежах).
# Порядок ВАЖЕН: более длинные варианты проверяются первыми, т.к.
# search_for("Подп.") матчит и префикс слова «Подпись» — иначе колонка
# определялась бы по укороченному rect'у и подпись смещалась.
#search_for() работает как подстрочный поиск, поэтому достаточно
# корневых вариантов «Подп»/«Подпис» — они покрывают и «Подп.», и «Подпись».
SIGNATURE_COLUMN_HEADER_ALTS: tuple[str, ...] = ("Подписи", "Подпис", "Подп")
# Допустимая ширина колонки «Подпись», мм (15–60 мм по типовым ГОСТ-штампам)
SIG_COLUMN_MIN_WIDTH_MM = 10.0  # минимальная ширина колонки «Подпись» (запас под мелкие штампы)
SIG_COLUMN_MAX_WIDTH_MM = 60.0

# ---------------------------------------------------------------------------
# ПОЗИЦИОНИРОВАНИЕ ПОДПИСИ В ЯЧЕЙКЕ «ПОДПИСЬ» (колонка справа от фамилии)
# ---------------------------------------------------------------------------
# Минимальная ширина целевой ячейки колонки «Подпись», мм (требование ТЗ).
# Если сетка распознана и следующая ячейка уже этой ширины — подпись
# вставляется точно в неё и центрируется по горизонтали и вертикали.
MIN_SIGNATURE_CELL_WIDTH_MM = 15.0
MIN_SIGNATURE_CELL_WIDTH_PT = MIN_SIGNATURE_CELL_WIDTH_MM * MM_TO_PT  # ≈42.5 pt

# Минимальная доля площади ячейки, которую должен занять графический объект,
# чтобы ячейка считалась занятой (мелкие штрихи/артефакты игнорируются)
MIN_GRAPHIC_AREA_RATIO = 0.30

# Допуск при поиске границ ячеек по линиям сетки, пунктов (стабилизация
# против разброса координат линий на 1-2 пункта).
CELL_SEARCH_TOLERANCE_PT = 2.0

# Максимальный зазор между строками, которые считаются ОДНОЙ ячейкой
# таблицы. Строки разных строк штампа («Разработал»/«Проверил») разделены
# горизонтальной линией сетки с зазором ~2-4 pt — такие кандидаты не
# объединяются, иначе два вхождения одной фамилии сливались бы в один блок
# и подпись ставилась только у первого из них.
MAX_LINE_GAP_WITHIN_CELL_PT = 8.0

# ---------------------------------------------------------------------------
# РУЧНОЙ РЕЖИМ (FALLBACK): вставка по фиксированным отступам страницы.
# Используется, если штамп не распознан и включён чекбокс «Ручной режим».
# ---------------------------------------------------------------------------

# Горизонтальный отступ от правого края страницы (в пунктах)
RIGHT_MARGIN_PT = 400

# Описание 4 мест вставки подписей (ручной режим).
# Каждый элемент кортежа:
#   (имя_подписанта, отступ_снизу_в_пунктах)
# где имя_подписанта: 1 — Подписант 1, 2 — Подписант 2.
SIGNATURE_SLOTS = (
    (1, 1),    # Место №1: Подписант 1, 7 pt от нижнего края
    (2, 13),   # Место №2: Подписант 2, 14 pt от нижнего края
    (2, 57),   # Место №3: Подписант 2, 21 pt от нижнего края
    (1, 70),   # Место №4: Подписант 1, 28 pt от нижнего края
)


# ============================================================================
# ИСКЛЮЧЕНИЕ: ШТАМП НЕ НАЙДЕН
# ============================================================================

class StampNotFoundError(Exception):
    """Штамп на странице не распознан (ключевые слова отсутствуют)."""


# ============================================================================
# ЛОГИКА: автоматическое распознавание фамилий в штампе
# ============================================================================

def _get_page_tables(page: fitz.Page):
    """Возвращает объект результата page.find_tables() (PyMuPDF >= 1.23)
    либо None, если find_tables недоступна/завершилась ошибкой.

    Кэшируется на странице (find_tables вызывается и для фильтра,
    и для извлечения сетки ячеек).
    """
    cached = getattr(page, "_find_tables_cache", "__unset__")
    if cached != "__unset__":
        return cached
    result = None
    if not hasattr(page, "find_tables"):
        logger.debug("page.find_tables недоступен в этой версии PyMuPDF")
    else:
        try:
            result = page.find_tables()
        except Exception as e:  # защита от сбоев парсера таблиц
            logger.warning("find_tables() завершился ошибкой: %s", e)
            result = None
    try:
        page._find_tables_cache = result
    except Exception:
        pass
    return result


def _table_grid_lines(table) -> tuple[list[float], list[float]]:
    """Извлекает координаты линий сетки одной таблицы find_tables:
    xs — границы колонок, ys — границы строк."""
    xs: set[float] = set()
    ys: set[float] = set()
    try:
        for c in table.cells:
            r = fitz.Rect(c)
            xs.add(round(r.x0, 2)); xs.add(round(r.x1, 2))
            ys.add(round(r.y0, 2)); ys.add(round(r.y1, 2))
    except Exception:
        pass
    return sorted(xs), sorted(ys)


def _get_page_tables_bboxes(page: fitz.Page) -> Optional[list[fitz.Rect]]:
    """Возвращает список bounding box'ов таблиц на странице через
    page.find_tables() (PyMuPDF >= 1.23).

    Returns:
        Список fitz.Rect (может быть пустым), либо None, если find_tables()
        недоступна в данной версии PyMuPDF или завершилась ошибкой —
        это сигнал использовать fallback-критерий соседних слов.
    """
    tables_obj = _get_page_tables(page)
    if tables_obj is None:
        return None
    bboxes: list[fitz.Rect] = []
    for tab in tables_obj.tables:
        try:
            bboxes.append(fitz.Rect(tab.bbox) & page.rect)
        except Exception:
            continue
    logger.info("На странице найдено таблиц: %d", len(bboxes))
    if not bboxes:
        # find_tables не сработал (например, на перегруженной фигурами
        # странице) — резерв: внешние рамки замкнутых контуров из
        # get_drawings в зоне штампа. Это позволяет фильтру штампа
        # корректно распознавать таблицы даже при сбое find_tables.
        bboxes = _get_drawing_table_bboxes(page)
        if bboxes:
            logger.info("Резерв по векторным рамкам: %d прямоугольник(ов) "
                        "таблиц в зоне штампа", len(bboxes))
    return bboxes


def _get_drawing_table_bboxes(page: fitz.Page) -> list[fitz.Rect]:
    """Резервный поиск рамок таблиц по векторным контурам get_drawings().

    Возвращает объединённые bounding box'ы крупных замкнутых контуров
    (прямоугольников/сеток) в нижней правой зоне страницы — область
    расположения ГОСТ-штампа. Используется, когда page.find_tables()
    ничего не находит (перегруженные фигурами страницы).
    """
    if not hasattr(page, "get_drawings"):
        return []
    try:
        drawings = page.get_drawings()
    except Exception as e:
        logger.warning("get_drawings() завершился ошибкой: %s", e)
        return []
    zone_y0 = STAMP_ZONE_BOTTOM_RATIO * page.rect.height - 60.0
    rects: list[fitz.Rect] = []
    for item in drawings:
        rect = item.get("rect")
        if rect is None:
            continue
        # Только крупные контуры в зоне штампа
        if rect.width < 40.0 or rect.height < 20.0:
            continue
        if rect.y1 < zone_y0:
            continue
        if rect.x1 < STAMP_ZONE_RIGHT_RATIO * page.rect.width - 80.0:
            continue
        rects.append(fitz.Rect(rect) & page.rect)
    merged: list[fitz.Rect] = []
    for r in rects:
        for i, m in enumerate(merged):
            if r.intersects(m) or (r & m).get_area() > 0:
                merged[i] = m | r
                break
        else:
            merged.append(r)
    # После слияния могли появиться очень крупные области — оставляем только
    # разумные рамки (не больше половины площади страницы)
    page_area = page.rect.get_area()
    return [m for m in merged if 0 < m.get_area() <= page_area]


def _is_inside_any_table(rect: fitz.Rect,
                         table_bboxes: list[fitz.Rect]) -> bool:
    """Проверяет, попадает ли центр Rect фамилии внутрь хотя бы одной таблицы."""
    center = fitz.Point((rect.x0 + rect.x1) / 2.0,
                        (rect.y0 + rect.y1) / 2.0)
    return any(center in tb for tb in table_bboxes)


def _has_stamp_neighbor_word(page: fitz.Page, rect: fitz.Rect) -> bool:
    """Fallback-критерий «фамилия внутри штампа»: ищет рядом с Rect фамилии
    (по X ±NEIGHBOR_RADIUS_X_PT, по Y ±NEIGHBOR_RADIUS_Y_PT) хотя бы одно
    слово-ориентир ячеек ГОСТ-штампа (STAMP_NEIGHBOR_WORDS).

    Зона поиска расширена на ширину строки текста слева/справа от фамилии,
    чтобы охватить соседнюю ячейку таблицы (подписи в ГОСТ-штампе обычно
    идут парами «Разработал | <фамилия>» в одной строке).
    """
    zone = fitz.Rect(rect.x0 - NEIGHBOR_RADIUS_X_PT - rect.width,
                     rect.y0 - NEIGHBOR_RADIUS_Y_PT,
                     rect.x1 + NEIGHBOR_RADIUS_X_PT + rect.width,
                     rect.y1 + NEIGHBOR_RADIUS_Y_PT)
    for word in STAMP_NEIGHBOR_WORDS:
        try:
            hits = page.search_for(word)
        except Exception:
            return False
        for hit in hits:
            if hit.intersects(zone):
                logger.debug("Рядом с фамилией найдено слово штампа '%s'", word)
                return True
    return False


def _normalize_line_value(v: float) -> int:
    """Округляет координату линии сетки до ЦЕЛОГО числа пунктов.

    Линии сетки на разных страницах одного документа могут иметь микроскопический
    разброс координат (например, 100.01 и 100.02 pt из-за антиалиасинга /
    неточного распознавания). Округление до целого приводит их к одному значению,
    поэтому границы ячеек определяются одинаково на всех страницах и подписи
    не «пляшут».
    """
    return int(round(float(v)))


def _is_valid_grid_pair(obj) -> bool:
    """True, если obj — корректная пара списков линий сетки (xs, ys).

    Валидация защищает от ValueError "not enough values to unpack
    (expected 2, got N)" / "(expected 3, got 2)" при строгой распаковке
    `xs, ys = grid_lines` в геометрических хелперах: допускается ТОЛЬКО
    последовательность из ровно двух элементов, каждый из которых —
    список/кортеж чисел. Ничего другого (строку, dict, одиночный Rect,
    пару разной длины) считаем некорректным форматом.
    """
    if not isinstance(obj, (list, tuple)) or len(obj) != 2:
        return False
    for seq in obj:
        if not isinstance(seq, (list, tuple)):
            return False
        for v in seq:
            try:
                float(v)
            except (TypeError, ValueError):
                return False
    return True


def _is_point_pair(p1, p2) -> bool:
    """True, если p1 и p2 — точки (объекты с числовыми .x/.y либо пары чисел).

    Защита от «not enough values to unpack (expected 3, got 2)» и подобных
    ошибок при разборе сегментов page.get_drawings(): элементы списка "items"
    могут иметь неожиданный формат (кривые Безье, пустые кортежи), поэтому
    перед распаковкой и обращением к .x/.y каждый сегмент валидируется.
    """
    for p in (p1, p2):
        if isinstance(p, (fitz.Point,)):
            continue
        if hasattr(p, "x") and hasattr(p, "y"):
            try:
                float(p.x)
                float(p.y)
            except (TypeError, ValueError):
                return False
            continue
        if (isinstance(p, (list, tuple)) and len(p) == 2):
            try:
                float(p[0])
                float(p[1])
            except (TypeError, ValueError):
                return False
            continue
        return False
    return True


def _normalize_grid_lines(grid_lines):
    """Приводит линии сетки к каноническому формату или None.

    Принимает:
      * пару списков (xs, ys) — возвращается как есть (валидный формат);
      * список bounding box'ов таблиц (fitz.Rect) — границы колонок/строк
        извлекаются из x0/x1 и y0/y1 прямоугольников;
      * любой другой/битый формат — возвращается None (вместо падения с
        ValueError "not enough values to unpack").
    """
    if _is_valid_grid_pair(grid_lines):
        return (list(grid_lines[0]), list(grid_lines[1]))
    if (isinstance(grid_lines, (list, tuple)) and len(grid_lines) > 0
            and all(isinstance(tb, fitz.Rect) for tb in grid_lines)):
        rx = sorted({float(v) for tb in grid_lines for v in (tb.x0, tb.x1)})
        ry = sorted({float(v) for tb in grid_lines for v in (tb.y0, tb.y1)})
        return (rx, ry)
    return None


def _get_cell_lines(page: fitz.Page) -> Optional[tuple[list[float], list[float]]]:
    """Собирает координаты линий сетки ячеек штампа.

    Источник 1 (предпочтительный): границы колонок/строк таблиц, найденных
    page.find_tables() (атрибут table.cells).
    Источник 2 (резерв, если find_tables недоступна или ничего не нашла):
    стороны замкнутых прямоугольных контуров из page.get_drawings().

    Все координаты нормализуются (округляются до целого пункта) и объединяются
    с допуском ~1.5 pt (_dedupe_lines) — это устраняет нестабильность границ
    ячеек при разбросе линий на 1-2 пункта между страницами.

    Результат кэшируется на странице.

    Returns:
        (xs, ys) — отсортированные X-координаты вертикальных линий и
        Y-координаты горизонтальных линий; None, если линии найти не удалось.
    """
    cache = getattr(page, "_cell_lines_cache", None)
    # Кэш может содержать некорректный формат (например, пару списков разной
    # длины или объект с числом элементов != 2). Строгая распаковка вида
    # `xs, ys = result` в таком случае вызывает ValueError
    # "not enough values to unpack (expected 2, got N)" / "(expected 3, got 2)".
    # Валидируем кэш: принимаем только корректную пару списков, иначе —
    # пересобираем линии сетки заново.
    if cache is not None and _is_valid_grid_pair(cache):
        return cache
    if cache is not None:
        logger.debug("Кэш линий сетки имеет неожиданный формат (%s) — "
                     "пересбор линий (защита от ValueError при распаковке)",
                     type(cache).__name__)
    xs: set[float] = set()
    ys: set[float] = set()

    # --- Источник 1: сетка таблиц find_tables (координаты строк/столбцов) ---
    tables_obj = _get_page_tables(page)
    if tables_obj is not None:
        for tab in tables_obj.tables:
            try:
                colx, rowy = tab.rows_cols_coordinates()
            except Exception:
                colx, rowy = [], []
                txs, tys = _table_grid_lines(tab)
                colx = [x for x in txs if x not in ("", None)]
                rowy = tys
            xs.update(_normalize_line_value(x) for x in colx)
            ys.update(_normalize_line_value(y) for y in rowy)

    # --- Источник 2: векторные рамки get_drawings (резерв/дополнение) ---
    if (not xs or not ys) and hasattr(page, "get_drawings"):
        try:
            drawings = page.get_drawings()
        except Exception as e:
            logger.warning("get_drawings() завершился ошибкой: %s", e)
            drawings = []
        # Ограничение области штампа: на перегруженных страницах с тысячами
        # фигур рассматриваются только контуры в нижней/правой зоне — это
        # резко сокращает объём разбора сегментов и предотвращает зависание.
        zone_y0 = STAMP_ZONE_BOTTOM_RATIO * page.rect.height - 60.0
        for item in drawings:
            rect = item.get("rect")
            if rect is None:
                continue
            # Пропуск мелких объектов и фигур вне зоны штампа ДО разбора
            # сегментов (в т.ч. одиночных линий, у которых одна из сторон
            # rect равна нулю — проверка width/height их бы отбросила).
            if rect.x1 < STAMP_ZONE_RIGHT_RATIO * page.rect.width - 80.0:
                continue
            if rect.y1 < zone_y0:
                continue
            if rect.width < 5.0 and rect.height < 5.0:
                continue  # мелкие точки/штрихи игнорируются
            if item.get("type") not in ("s", "f"):
                continue  # обведённые/залитые контуры
            items_list = item.get("items", ())
            # Защита от «not enough values to unpack (expected 3, got 2)» /
            # «too many values to unpack»: распаковываем ТОЛЬКО сегменты из
            # ровно трёх частей; кривые Безье ('c'/'qu', 4+ элемента),
            # прямоугольники ('re', 2 элемента) и пустые элементы пропускаются.
            for seg in items_list:
                if not isinstance(seg, (list, tuple)) or len(seg) != 3:
                    continue
                itype, p1, p2 = seg
                if itype != "l":
                    continue
                if not _is_point_pair(p1, p2):
                    continue
                # Приводим точки к fitz.Point (поддержка формата (x, y))
                if not isinstance(p1, fitz.Point):
                    p1 = fitz.Point(float(p1.x if hasattr(p1, "x") else p1[0]),
                                    float(p1.y if hasattr(p1, "y") else p1[1]))
                if not isinstance(p2, fitz.Point):
                    p2 = fitz.Point(float(p2.x if hasattr(p2, "x") else p2[0]),
                                    float(p2.y if hasattr(p2, "y") else p2[1]))
                dx = abs(p2.x - p1.x)
                dy = abs(p2.y - p1.y)
                # Координаты линии берём напрямую из сегмента: rect фигуры
                # может быть «вырожденным» (нулевая ширина/высота у одиночной
                # линии), поэтому сравнение с границами rect не выполняем.
                if dy < 0.6 and dx >= 5.0:
                    ys.add(_normalize_line_value((p1.y + p2.y) / 2.0))
                elif dx < 0.6 and dy >= 5.0:
                    xs.add(_normalize_line_value((p1.x + p2.x) / 2.0))

    # Координаты линий округляются до ЦЕЛОГО пункта и близкие значения
    # (разброс 1-2 pt) объединяются — границы ячеек определяются одинаково
    # на всех страницах документа, подписи не «пляшут»
    xs = sorted({_normalize_line_value(v) for v in _dedupe_lines(list(xs))})
    ys = sorted({_normalize_line_value(v) for v in _dedupe_lines(list(ys))})

    result = (xs, ys)
    try:
        page._cell_lines_cache = result
    except Exception:
        pass
    # Диагностика: координаты всех найденных линий сетки штампа — в лог
    logger.info("Линии сетки штампа — вертикальные X: %s",
                ["%.1f" % x for x in result[0]])
    logger.info("Линии сетки штампа — горизонтальные Y: %s",
                ["%.1f" % y for y in result[1]])
    return result if (xs or ys) else None


def _snap_line(coord: float, lines: list[float],
               tol: float = CELL_SEARCH_TOLERANCE_PT) -> Optional[float]:
    """Возвращает ближайшую линию сетки к coord (не дальше tol), либо None."""
    best: Optional[float] = None
    for x in lines:
        d = abs(x - coord)
        if d <= tol and (best is None or d < abs(best - coord)):
            best = x
    return best


def _dedupe_lines(lines: list[float]) -> list[float]:
    """Объединяет близкие линии сетки (разброс 1-2 пункта из-за неточного
    распознавания) в одну — среднее арифметическое группы. Это стабилизирует
    позиционирование подписей на разных страницах одного документа."""
    result: list[float] = []
    for v in sorted(lines):
        if result and abs(v - result[-1][-1]) <= 1.5:
            result[-1].append(v)
        else:
            result.append([v])
    return [round(sum(g) / len(g), 2) for g in result]


def _find_containing_cell(rect: fitz.Rect,
                          lines: list[fitz.Rect] | tuple[list[float], list[float]]
                          ) -> Optional[fitz.Rect]:
    """Находит прямоугольник ячейки, содержащий rect фамилии.

    Принимает либо список bounding box'ов таблиц (fitz.Rect), либо пару
    списков координат линий сетки (xs, ys) от _get_cell_lines().
    Границы ищутся с допуском ±CELL_SEARCH_TOLERANCE_PT (стабилизация
    против разброса координат линий на 1-2 пункта)."""
    cx = (rect.x0 + rect.x1) / 2.0
    cy = (rect.y0 + rect.y1) / 2.0

    # Вариант 1: список Rect'ов (bounding box'ы таблиц find_tables)
    if lines and isinstance(lines[0], fitz.Rect):
        for tb in lines:
            if tb.contains(fitz.Point(cx, cy)):
                return fitz.Rect(tb)
        return None

    # Вариант 2: линии сетки (xs, ys) из get_drawings/find_tables.
    # Защита от неожиданных форматов ("not enough values to unpack"):
    # нормализуем вход к паре списков; иначе — границы не определены.
    norm = _normalize_grid_lines(lines)
    if norm is None:
        logger.debug("_find_containing_cell: неожиданный формат линий (%s) — "
                     "ячейка по сетке не определена", type(lines).__name__)
        return None
    xs, ys = norm
    left = max((x for x in xs if x <= cx + CELL_SEARCH_TOLERANCE_PT),
               default=None)
    right = min((x for x in xs if x >= cx - CELL_SEARCH_TOLERANCE_PT),
                default=None)
    top = max((y for y in ys if y <= cy + CELL_SEARCH_TOLERANCE_PT),
              default=None)
    bottom = min((y for y in ys if y >= cy - CELL_SEARCH_TOLERANCE_PT),
                 default=None)
    if left is None or right is None or top is None or bottom is None:
        return None
    cell = fitz.Rect(left, top, right, bottom)
    if cell.width < 3.0 or cell.height < 3.0 or not cell.contains(fitz.Point(cx, cy)):
        return None
    return cell


def _row_bounds_at(y: float,
                   grid_lines: Optional[tuple]
                   ) -> tuple[Optional[float], Optional[float]]:
    """Границы СТРОКИ таблицы вокруг точки с координатой Y: (row_top, row_bottom).
    Строки разных строк штампа не смешиваются.

    Устойчивость к формату источника (защита от ValueError "not enough
    values to unpack"): принимает либо пару списков линий (xs, ys), либо
    список bounding box'ов таблиц (fitz.Rect) — из Rect'ов извлекаются
    горизонтальные границы y0/y1."""
    if not grid_lines:
        return None, None
    # Список Rect'ов (bbox'ы таблиц find_tables) вместо линий сетки
    if isinstance(grid_lines, (list, tuple)) and \
            len(grid_lines) > 0 and isinstance(grid_lines[0], fitz.Rect):
        ys: list[float] = []
        for tb in grid_lines:
            ys.append(float(tb.y0))
            ys.append(float(tb.y1))
    elif isinstance(grid_lines, (list, tuple)) and len(grid_lines) >= 2 \
            and isinstance(grid_lines[1], (list, tuple)):
        ys = list(grid_lines[1])
    else:
        logger.debug("_row_bounds_at: неожиданный формат линий сетки (%s) — "
                     "границы строки не определены", type(grid_lines).__name__)
        return None, None
    cand_t = [yy for yy in ys if yy <= y + CELL_SEARCH_TOLERANCE_PT]
    cand_b = [yy for yy in ys if yy >= y - CELL_SEARCH_TOLERANCE_PT]
    if cand_t and cand_b:
        return max(cand_t), min(cand_b)
    return None, None


def _row_bounds(block: fitz.Rect,
                grid_lines: Optional[tuple[list[float], list[float]]],
                fallback: Optional[fitz.Rect] = None
                ) -> tuple[Optional[float], Optional[float]]:
    """Границы СТРОКИ таблицы вокруг блока текста (см. _row_bounds_at).

    Если горизонтальные линии строки не распознаны — используется резерв:
    границы ячейки `fallback` (если она найдена), иначе вертикальные границы
    самого блока текста с небольшим допуском. Это гарантирует, что подпись
    центрируется по реальной строке фамилии, а не «уплывает» вверх/вниз."""
    top, bottom = _row_bounds_at((block.y0 + block.y1) / 2.0, grid_lines)
    if top is not None and bottom is not None:
        return top, bottom
    if fallback is not None and fallback.height > 3.0:
        logger.debug("Линии строки не найдены — резерв по границам ячейки "
                     "(y=%.1f..%.1f)", fallback.y0, fallback.y1)
        return fallback.y0, fallback.y1
    if block.height > 3.0:
        logger.debug("Линии строки и ячейка не найдены — резерв по блоку "
                     "текста (y=%.1f..%.1f)", block.y0 - 2.0, block.y1 + 2.0)
        return block.y0 - 2.0, block.y1 + 2.0
    return None, None


def _is_cell_empty(page: fitz.Page, cell: fitz.Rect) -> bool:
    """Проверяет, что ячейка пустая (нет значимого содержимого внутри).

    Перед проверкой rect уменьшается на 2 пункта с каждой стороны, чтобы
    не захватить пограничные линии сетки и соседние ячейки. Текст внутри
    делает ячейку занятой. Графические объекты учитываются только если
    занимают >= 30% площади ячейки (мелкие штрихи, точки и артефакты
    распознавания сетки игнорируются — иначе реальные штампы с лёгкими
    начертаниями ошибочно считаются «занятыми» и подписи пропускаются).
    Объекты, совпадающие с рамками самой ячейки (линии сетки), всегда
    игнорируются."""
    inner = fitz.Rect(cell.x0 + 2.0, cell.y0 + 2.0,
                      cell.x1 - 2.0, cell.y1 - 2.0)
    if inner.is_empty or inner.width <= 0 or inner.height <= 0:
        return True
    try:
        text = page.get_text("text", clip=inner).strip()
    except Exception:
        return False
    if text:
        logger.debug("Ячейка (%.1f; %.1f) содержит текст '%s' — занята",
                     cell.x0, cell.y0, text[:40])
        return False
    # Проверка графических объектов внутри ячейки (подписи-картинки, линии
    # подписей от руки), не считая самих рамок ячейки
    cell_area = max(inner.width * inner.height, 1.0)
    min_obj_area = MIN_GRAPHIC_AREA_RATIO * cell_area
    try:
        drawings = page.get_drawings(clip=inner)
    except Exception:
        drawings = []
    for item in drawings:
        r = item.get("rect")
        if r is None:
            continue
        # Игнорируем объекты, совпадающие с рамками ячейки (линии сетки)
        if abs(r.width - cell.width) < 3.0 and abs(r.height - cell.height) < 3.0:
            continue
        obj_area = max(r.width, 0.0) * max(r.height, 0.0)
        # Мелкие объекты (< порога площади) не считаются занятившими ячейку
        if obj_area < min_obj_area:
            continue
        if r.width >= 2.0 and r.height >= 2.0:
            logger.debug("В целевой ячейке найден графический объект "
                         "(%.1f; %.1f)-(%.1f; %.1f), площадь %.0f pt^2 "
                         "(>= %.0f%% ячейки) — ячейка занята",
                         r.x0, r.y0, r.x1, r.y1, obj_area,
                         MIN_GRAPHIC_AREA_RATIO * 100)
            return False
    return True


def _find_signature_cell(rect: fitz.Rect, cell: fitz.Rect,
                         grid_lines: tuple[list[float], list[float]]
                         ) -> Optional[fitz.Rect]:
    """Находит ячейку справа от ячейки с фамилией в той же строке.

    Args:
        rect: bounding box фамилии.
        cell: ячейка, содержащая фамилию.
        grid_lines: (xs, ys) — координаты линий сетки.

    Returns:
        fitz.Rect целевой ячейки (колонка "Подпись") или None.
    """
    # Защита от неожиданных форматов ("not enough values to unpack"):
    # нормализуем линии сетки к паре списков (xs, ys); при битом формате —
    # целевая ячейка не определена.
    norm = _normalize_grid_lines(grid_lines)
    if norm is None:
        logger.debug("_find_signature_cell: неожиданный формат линий сетки "
                     "(%s) — целевая ячейка не определена",
                     type(grid_lines).__name__)
        return None
    xs, ys = norm

    # Находим строку ячейки с фамилией (по Y-координатам)
    cy = (cell.y0 + cell.y1) / 2.0
    row_top = max((y for y in ys if y <= cy + 1.0), default=None)
    row_bottom = min((y for y in ys if y >= cy - 1.0), default=None)

    if row_top is None or row_bottom is None:
        return None

    # Находим правую границу ячейки с фамилией
    cx = (cell.x0 + cell.x1) / 2.0
    cell_right = min((x for x in xs if x >= cx - 1.0), default=None)

    if cell_right is None:
        return None

    # Находим следующую вертикальную линию правее (левая граница целевой ячейки)
    target_left = min((x for x in xs if x >= cell_right + 1.0), default=None)

    if target_left is None:
        return None

    # Находим правую границу целевой ячейки
    target_right = min((x for x in xs if x >= target_left + 5.0), default=None)

    if target_right is None:
        return None

    return fitz.Rect(target_left, row_top, target_right, row_bottom)


def _find_signature_column_cell(
    page: fitz.Page, block: fitz.Rect, name_cell: fitz.Rect,
    grid_lines: Optional[tuple[list[float], list[float]]],
    sig_col_x: Optional[tuple[float, float]] = None,
    rect: Optional[fitz.Rect] = None,
) -> tuple[Optional[fitz.Rect], str]:
    """Ищет целевую ячейку колонки «Подпись» — в ТОЙ ЖЕ строке, что и
    фамилия.

    Шаг 0 (приоритет). Колонка «Подпись» найдена по заголовку в шапке
        штампа (_find_signature_column_x): её X-границы (sig_col_x)
        используются КАК ЕСТЬ, Y-границы — из горизонтальных линий сетки
        строки с фамилией. Это корректно работает даже при ОБЪЕДИНЁННОЙ
        ячейке с фамилией (колонки «Лист» + «№ док.»): подпись ставится
        через одну ячейку правее, точно в настоящую колонку «Подпись»,
        а НЕ в промежуточную служебную колонку «№ док.».

    Шаг 1. Прямой поиск следующей ячейки по линиям сетки
        (_find_signature_cell): левая граница целевой ячейки — следующая
        вертикальная линия после правой границы ячейки с фамилией; верх/низ —
        горизонтальные линии той же строки.

    Шаг 2. Проверка пустоты целевой ячейки (_is_cell_empty). Если следующая
        ячейка занята или слишком узкая — перебором вправо проверяются ещё
        до 3 соседних ячеек (в ГОСТ-штампе между фамилией и колонкой
        «Подпись» может быть служебная колонка «№ док.»).

    Returns:
        (cell | None, reason) — найденная ячейка либо причина отказа
        ("no_grid" / "no_cell" / "occupied"), для диагностики в логе.
    """
    # --- Шаг 0: колонка «Подпись», найденная по заголовку ---
    # X-границы колонки берются из заголовка шапки; если линии сетки
    # распознаны, они уточняются (snap) ближайшими вертикальными линиями
    # рядом с границами колонки. Сетка НЕ является обязательным условием:
    # без неё подписи всё равно встают в правильную колонку.
    if sig_col_x is not None:
        # Устойчивость к формату возврата: нормализуем значение колонки к
        # паре чисел (x0, x1). Строгая распаковка вида `a, b, c = sig_col_x`
        # или обращение к элементам без проверки длины вызывает ValueError
        # "not enough values to unpack (expected 3, got 2)" при неожиданном
        # формате — вместо падения колонка считается ненайденной.
        vals: list[float] = []
        if isinstance(sig_col_x, (list, tuple)) and len(sig_col_x) >= 2:
            try:
                vals = [float(v) for v in sig_col_x[:2]]
            except (TypeError, ValueError):
                vals = []
        else:
            logger.debug("sig_col_x имеет неожиданный формат (%r) — "
                         "колонка «Подпись» по заголовку проигнорирована",
                         sig_col_x)
        if len(vals) == 2 and vals[1] > vals[0]:
            col_x0, col_x1 = vals
        else:
            sig_col_x = None
    if sig_col_x is not None:
        norm_grid = _normalize_grid_lines(grid_lines)
        if norm_grid is not None:
            gxs = norm_grid[0]
            snapped0 = min((x for x in gxs if abs(x - col_x0) <= 2.0),
                           default=col_x0)
            snapped1 = min((x for x in gxs if abs(x - col_x1) <= 2.0),
                           default=col_x1)
            if snapped1 > snapped0:
                col_x0, col_x1 = snapped0, snapped1
        # СТРОКА определяется по ГОРИЗОНТАЛИ блока фамилии: строки штампа
        # имеют высоту заметно большую высоты текста, поэтому центр блока
        # гарантированно лежит внутри своей же строки. Раньше использовался
        # верх rect.y0 + 1.0 — при малой высоте строки это давало соседнюю
        # (вышестоящую) горизонтальную линию, и подпись «уплывала» вверх.
        # Блок ограничен границами строки данного вхождения (_merge_line_group),
        # поэтому объединение с соседними строками сюда не попадает.
        anchor_cy = (block.y0 + block.y1) / 2.0
        row_top, row_bottom = _row_bounds_at(anchor_cy, grid_lines)
        if row_top is not None and row_bottom is not None \
                and (row_bottom - row_top) > 2.0 * SIGNATURE_HEIGHT_PT:
            # Линии сетки дали полосу, охватывающую несколько строк штампа
            # (пропущена внутренняя горизонталь) — сужаем до ячейки/блока
            logger.debug("Полоса строки по линиям слишком высокая "
                         "(%.1f pt > 2×%.1f) — сужение",
                         row_bottom - row_top, SIGNATURE_HEIGHT_PT)
            row_top = row_bottom = None
        if row_top is None or row_bottom is None:
            # Горизонтальные линии строки не распознаны — резерв:
            # границы ячейки с фамилией (если есть), иначе вертикальные
            # границы блока фамилии с допуском, чтобы подпись
            # центрировалась на уровне самой фамилии
            if name_cell is not None and name_cell.height > 3.0:
                row_top, row_bottom = name_cell.y0, name_cell.y1
            else:
                row_top = block.y0 - 2.0
                row_bottom = block.y1 + 2.0
        col_cell = fitz.Rect(col_x0, row_top, col_x1, row_bottom)
        if col_cell.width >= 3.0 and col_cell.height >= 3.0:
            empty = _is_cell_empty(page, col_cell)
            logger.info("Целевая ячейка «Подпись» (по заголовку колонки): "
                        "(%.1f; %.1f)-(%.1f; %.1f), ширина %.1f pt, пустая=%s",
                        col_cell.x0, col_cell.y0, col_cell.x1, col_cell.y1,
                        col_cell.width, empty)
            if empty:
                return col_cell, ""
            # Колонка найдена, но ячейка занята — перебирать вправо нельзя:
            # следующая колонка это «Дата», ставить подпись туда некорректно
            return None, "occupied"
        logger.debug("Колонка «Подпись» найдена, но целевая ячейка слишком "
                     "мала (%.1f x %.1f pt) — переход к поиску по сетке",
                     col_cell.width, col_cell.height)

    if not grid_lines:
        return None, "no_grid"
    # Устойчивость к формату: (xs, ys) — линии сетки; список fitz.Rect —
    # bbox'ы таблиц (внешние границы используются как колонки/строки).
    # Защита от ValueError "not enough values to unpack (expected 2/3...)":
    # нормализация возвращает None при любом битом формате вместо падения.
    norm = _normalize_grid_lines(grid_lines)
    if norm is None:
        logger.debug("_find_signature_column_cell: неожиданный формат "
                     "линий сетки (%s) — поиск по сетке пропущен",
                     type(grid_lines).__name__)
        return None, "no_grid"
    xs, ys = norm
    grid_lines = norm

    # --- Шаг 1: следующая ячейка в той же строке по линиям сетки ---
    target = _find_signature_cell(block, name_cell, grid_lines)
    if target is not None and target.width >= 3.0 \
            and target.height >= 3.0:
        # СТРОГАЯ ПРОВЕРКА «ТА ЖЕ СТРОКА» (требование 6): ячейка из Шага 1
        # принимается только если её вертикальный центр лежит на уровне
        # центра блока фамилии (в пределах 0.6 высоты строки). Иначе —
        # multi-row ячейка сетки (пропущена внутренняя горизонтальная
        # линия) охватывает несколько строк штампа, и подпись «уплывёт»
        # вверх/вниз от своей строки; переходим к Шагу 2 с сужением полосы.
        cand_cy = (target.y0 + target.y1) / 2.0
        block_cy = (block.y0 + block.y1) / 2.0
        row_h = max(block.height, 10.0)
        same_row = abs(cand_cy - block_cy) <= row_h * 0.6
        empty = _is_cell_empty(page, target)
        logger.info("Целевая ячейка «Подпись» (следующая по сетке): "
                    "(%.1f; %.1f)-(%.1f; %.1f), ширина %.1f pt, пустая=%s, "
                    "та же строка=%s",
                    target.x0, target.y0, target.x1, target.y1,
                    target.width, empty, same_row)
        if empty and same_row:
            return target, ""

    # --- Шаг 2: резервный перебор соседних ячеек вправо (до 3) ---
    row_top, row_bottom = _row_bounds(block, grid_lines, name_cell)
    if row_top is None or row_bottom is None:
        return (target, "") if target is not None else (None, "no_cell")

    # Защита от multi-row ячеек: если найденные границы строки охватывают
    # больше одной реальной строки штампа (высота > 2× высоты подписи),
    # сужаем полосу до фактических границ блока фамилии — иначе подпись
    # центрируется по нескольким строкам и «уплывает» вверх/вниз
    if (row_bottom - row_top) > 2.0 * SIGNATURE_HEIGHT_PT and block.height > 3.0:
        logger.debug("Полоса строки слишком высокая (%.1f pt > 2×%.1f) — "
                     "сужение до границ блока (%.1f..%.1f)",
                     row_bottom - row_top, SIGNATURE_HEIGHT_PT,
                     block.y0 - 2.0, block.y1 + 2.0)
        row_top = max(row_top, block.y0 - 2.0)
        row_bottom = min(row_bottom, block.y1 + 2.0)

    # Вертикальные границы колонок должны лежать в диапазоне строк штампа
    col_cands = [x for x in xs if row_top - 0.5 <= x <= row_bottom + 0.5]
    col_cands = sorted(set(col_cands))

    # Перебираем ячейки, начинающиеся не левее правой границы ячейки имени
    # (допуск 1 pt на разброс линий), идём вправо до 3 ячеек.
    start_x = name_cell.x1 - 1.0
    idxs = [i for i, x in enumerate(col_cands) if x >= start_x]
    for i in idxs[:3]:
        if i + 1 >= len(col_cands):
            break
        cand = fitz.Rect(col_cands[i], row_top, col_cands[i + 1], row_bottom)
        if cand.width < 3.0:
            continue
        # СТРОГАЯ ПРОВЕРКА «ТА ЖЕ СТРОКА»: центр кандидата должен лежать
        # на уровне центра блока фамилии (в пределах 0.6 высоты строки).
        # Это исключает вставку подписи в соседнюю/пустую строку штампа
        # (например, между «Гл.констр.» и «Н.контр.»), если границы строки
        # были распознаны неточно и полоса row_top..row_bottom смещена.
        cand_cy = (cand.y0 + cand.y1) / 2.0
        block_cy = (block.y0 + block.y1) / 2.0
        row_h = max(block.height, 10.0)
        if abs(cand_cy - block_cy) > row_h * 0.6:
            logger.debug("Ячейка (%.1f; %.1f)-(%.1f; %.1f) — другая строка "
                         "(|Δcy|=%.1f > %.1f): пропуск",
                         cand.x0, cand.y0, cand.x1, cand.y1,
                         abs(cand_cy - block_cy), row_h * 0.6)
            continue
        empty = _is_cell_empty(page, cand)
        wide_enough = cand.width >= MIN_SIGNATURE_CELL_WIDTH_PT
        logger.info("Проверка ячейки (%.1f; %.1f)-(%.1f; %.1f): ширина %.1f pt,"
                    " пустая=%s, достаточно широкая=%s",
                    cand.x0, cand.y0, cand.x1, cand.y1, cand.width,
                    empty, wide_enough)
        if empty and wide_enough:
            return cand, ""

    # Ни одна подходящая пустая ячейка не найдена — возвращаем первую
    # найденную по сетке (будет проведено резервное позиционирование)
    if target is not None:
        return None, "occupied"
    return None, "no_cell"


def _find_sig_column_by_date(
    page: fitz.Page,
    xs: list[float],
    page_height: float,
) -> Optional[tuple[float, float]]:
    """Эвристика «колонка слева от даты» (Сбой 4).

    Если заголовок «Подпись» не найден: ищет на странице слова-даты
    формата XX.XX / XX.XX.XXXX (DATE_CELL_PATTERN) в НИЖНЕЙ половине
    страницы, определяет ячейку каждой даты по вертикальным линиям сетки
    (xs) и берёт соседнюю ячейку СЛЕВА от неё — это колонка «Подпись».
    Ширина полученной колонки проверяется в пределах
    SIG_COLUMN_MIN_WIDTH_MM..SIG_COLUMN_MAX_WIDTH_MM.

    Args:
        page: страница PyMuPDF.
        xs: отсортированные X-координаты вертикальных линий сетки/таблиц.
        page_height: высота страницы (для фильтра нижней половины).

    Returns:
        (x0, x1) границы колонки «Подпись» либо None.
    """
    if len(xs) < 3:
        return None
    min_w = SIG_COLUMN_MIN_WIDTH_MM * MM_TO_PT
    max_w = SIG_COLUMN_MAX_WIDTH_MM * MM_TO_PT
    try:
        words = page.get_text("words")
    except Exception:
        return None

    # Подсчёт голосов: у настоящего штампа несколько дат в колонке —
    # выбираем вариант колонок, подтверждённый наибольшим числом дат
    votes: dict[tuple[float, float], int] = {}
    for w in words:
        text = w[4]
        if not DATE_CELL_PATTERN.match(text):
            continue
        wy = (w[1] + w[3]) / 2.0
        wx = (w[0] + w[2]) / 2.0
        # Только нижняя половина страницы (колонка «Дата» ГОСТ-штампа)
        if wy < 0.5 * page_height:
            continue
        # Ячейка даты: между ближайшими линиями сетки вокруг слова-даты
        left_lines = [x for x in xs if x <= wx + 1.0]
        right_lines = [x for x in xs if x >= wx - 1.0]
        if not left_lines or not right_lines:
            continue
        date_x0 = max(left_lines)
        date_x1 = min(right_lines)
        if date_x1 <= date_x0:
            continue
        # Ячейка СЛЕВА от даты — колонка «Подпись»
        sig_right = date_x0
        sig_lefts = [x for x in xs if x < sig_right - 1.0]
        if not sig_lefts:
            continue
        sig_x0 = max(sig_lefts)
        width = sig_right - sig_x0
        if width < min_w or width > max_w:
            logger.debug("Колонка «Подпись» (по дате '%s'): ширина %.1f pt "
                         "вне допуска [%.1f; %.1f] — кандидат отклонён",
                         text, width, min_w, max_w)
            continue
        key = (round(sig_x0, 1), round(sig_right, 1))
        votes[key] = votes.get(key, 0) + 1

    if not votes:
        return None
    best_key = max(votes, key=lambda k: votes[k])
    best = (best_key[0], best_key[1])
    best_count = votes[best_key]
    if best is not None:
        logger.info("Колонка 'Подпись' найдена (по дате, источник границ: "
                    "сетка): x=[%.1f; %.1f], ширина %.1f pt, дат-подтверждений %d",
                    best[0], best[1], best[1] - best[0], best_count)
    return best


def _find_sig_column_by_fallback(
    table_bboxes: Optional[list[fitz.Rect]],
    xs: list[float],
) -> Optional[tuple[float, float]]:
    """Третий fallback: «предпоследняя колонка таблицы» (Сбой 4).

    Если ни заголовок «Подпись», ни даты не найдены — берётся правая
    граница таблицы штампа и отступает влево на типичную ширину колонки
    «Дата» (DATE_COLUMN_TYPICAL_WIDTH_MM, допустимый разброс
    30–50 мм). Границы уточняются ближайшими линиями сетки.

    Returns:
        (x0, x1) границы колонки «Подпись» либо None.
    """
    bboxes = [tb for tb in (table_bboxes or []) if tb.width > 10.0]
    if not bboxes and len(xs) >= 2:
        bboxes = [fitz.Rect(min(xs), 0, max(xs), 1)]
    if not bboxes:
        return None
    # Правая граница самого правого bbox — внешний край колонки «Дата»
    right_edge = max(float(tb.x1) for tb in bboxes)
    min_dw = DATE_COLUMN_MIN_WIDTH_MM * MM_TO_PT
    max_dw = DATE_COLUMN_MAX_WIDTH_MM * MM_TO_PT
    typical_dw = DATE_COLUMN_TYPICAL_WIDTH_MM * MM_TO_PT
    min_sw = SIG_COLUMN_MIN_WIDTH_MM * MM_TO_PT
    max_sw = SIG_COLUMN_MAX_WIDTH_MM * MM_TO_PT

    # Левая граница колонки «Дата»: ближайшая линия сетки слева от
    # правого края на расстоянии типичной ширины даты (допуск 30–50 мм)
    date_x0 = right_edge - typical_dw
    cand_dates = [x for x in xs
                  if right_edge - max_dw <= x <= right_edge - min_dw]
    if cand_dates:
        date_x0 = min(cand_dates, key=lambda x: abs(x - (right_edge - typical_dw)))
    elif not any(x < right_edge - 1.0 for x in xs):
        logger.debug("Fallback «предпоследняя колонка»: нет линий левее "
                     "правого края %.1f", right_edge)
        return None

    # Колонка «Подпись» — между ближайшей линией слева от date_x0 и date_x0
    left_lines = [x for x in xs if x < date_x0 - 1.0]
    sig_x0 = max(left_lines) if left_lines else date_x0 - typical_dw
    width = date_x0 - sig_x0
    if width < min_sw or width > max_sw:
        # линии не дали разумной ширины — берём типовой отступ напрямую
        sig_x0 = date_x0 - typical_dw
        width = date_x0 - sig_x0
    if width < min_sw or width > max_sw:
        logger.debug("Fallback «предпоследняя колонка»: ширина %.1f pt вне "
                     "допуска [%.1f; %.1f] — отклонено", width, min_sw, max_sw)
        return None
    logger.info("Колонка 'Подпись' найдена (fallback: предпоследняя "
                "колонка таблицы): x=[%.1f; %.1f], ширина %.1f pt",
                sig_x0, date_x0, width)
    return (sig_x0, date_x0)


def _find_signature_column_x_by_header(
    page: fitz.Page,
    xs: list[float],
    source: str,
) -> Optional[tuple[float, float]]:
    """Канонический поиск колонки «Подпись» по заголовку в шапке штампа.

    Ищет слово SIGNATURE_COLUMN_HEADER («Подпись», варианты — «Подп.»,
    «Подписи») на странице, берёт вхождение в нижней половине листа
    (шапка ГОСТ-штампа), определяет, между какими вертикальными линиями
    сетки оно находится, и возвращает эти координаты.

    Такой подход надёжнее «ближайшей линии справа от фамилии»: фамилия
    может лежать в ОБЪЕДИНЁННОЙ ячейке (колонки «Лист» + «№ док.»), и
    внутренняя граница объединённой ячейки не является границей колонки
    «Подпись». Здесь же колонка определяется по её ЗАГОЛОВКУ.

    Args:
        page: страница PyMuPDF.
        xs: отсортированные X-границы колонок (линии сетки или таблицы).
        source: описание источника границ для лога ("сетка"/"границы таблиц").

    Returns:
        (x0, x1) — левая и правая граница колонки «Подпись», либо None,
        если заголовок или границы колонки найти не удалось.
    """
    # --- Поиск заголовка колонки ---
    # Собираем вхождения ВСЕХ вариантов («Подпись», «Подписи», «Подп.»...),
    # затем выбираем самое длинное: search_for("Подп") матчит и префикс
    # слова «Подпись», поэтому короткое укороченное rect'овое вхождение не
    # должно побеждать полное — иначе границы колонки определяются неверно
    # и подпись смещается.
    header_rect: Optional[fitz.Rect] = None
    best_term_len = -1
    for term in (SIGNATURE_COLUMN_HEADER,) + SIGNATURE_COLUMN_HEADER_ALTS:
        try:
            hits = page.search_for(term)
        except Exception:
            hits = []
        if not hits:
            continue
        logger.debug("Заголовок '%s': %d вход.(ий) на странице",
                     term, len(hits))
        # Только вхождения в нижней части страницы (шапка штампа всегда внизу)
        stamp_hits = [h for h in hits if h.y0 > 0.5 * page.rect.height] or hits
        # Среди них — самое широкое (длинное слово даёт больший rect)
        longest = max(stamp_hits, key=lambda r: r.width)
        if len(term) > best_term_len:
            best_term_len = len(term)
            header_rect = longest
    if header_rect is None:
        logger.debug("Заголовок «%s» (и варианты %s) на странице не найден",
                     SIGNATURE_COLUMN_HEADER,
                     ", ".join(SIGNATURE_COLUMN_HEADER_ALTS))
        return None

    logger.info("Заголовок колонки подписи определён: rect=(%.1f; %.1f; "
                "%.1f; %.1f)", header_rect.x0, header_rect.y0,
                header_rect.x1, header_rect.y1)

    # Вертикальные линии, между которыми находится заголовок
    left_lines = [x for x in xs if x <= header_rect.x0 + 1.0]
    right_lines = [x for x in xs if x >= header_rect.x1 - 1.0]
    if not left_lines or not right_lines:
        logger.debug("Колонка «Подпись»: заголовок (%.1f; %.1f) не ограничен "
                     "линиями сетки (%s)", header_rect.x0, header_rect.y0,
                     source)
        return None

    col_x0 = max(left_lines)
    col_x1 = min(right_lines)

    # Проверка разумности ширины колонки (15–60 мм по типовым ГОСТ-штампам);
    # если ближайшая правая линия слишком близко (объединённая ячейка шапки),
    # перебираем следующие линии вправо в пределах допустимой ширины
    min_w = SIG_COLUMN_MIN_WIDTH_MM * MM_TO_PT
    max_w = SIG_COLUMN_MAX_WIDTH_MM * MM_TO_PT
    for cand_r in (x for x in xs if x > col_x0):
        width = cand_r - col_x0
        if width > max_w:
            break
        if width >= min_w:
            col_x1 = cand_r
            break
    col_width = col_x1 - col_x0
    if col_width < min_w or col_width > max_w:
        logger.debug("Колонка «Подпись»: ширина %.1f pt вне допуска "
                     "[%.1f; %.1f] — отклонено", col_width, min_w, max_w)
        return None

    logger.info("Колонка 'Подпись' найдена (метод: заголовок, источник "
                "границ: %s): x=[%.1f; %.1f], ширина %.1f pt",
                source, col_x0, col_x1, col_width)
    return (col_x0, col_x1)


def _find_signature_column_x(
    page: fitz.Page,
    grid_lines: Optional[tuple[list[float], list[float]]],
    table_bboxes: Optional[list[fitz.Rect]],
) -> Optional[tuple[float, float]]:
    """Находит X-границы (x0, x1) колонки «Подпись» в штампе.

    Каскад методов (Сбой 4 — нестандартные штампы без заголовков колонок):
      1. По заголовку «Подпись»/«Подп.»/«Подписи» в шапке штампа
         (_find_signature_column_x_by_header) — канонический метод.
      2. Эвристика «колонка слева от даты» (_find_sig_column_by_date):
         слова-даты XX.XX / XX.XX.XXXX в нижней половине страницы,
         ячейка слева от даты, проверка ширины 10–60 мм.
      3. Fallback «предпоследняя колонка таблицы»
         (_find_sig_column_by_fallback): правый край таблицы минус
         типичная ширина колонки «Дата» (~30–50 мм).

    Обратная совместимость: сигнатура и тип возврата (Optional[tuple])
    не изменились; вызывающий код (`find_stamp_cells`, Шаг B) работает
    без изменений. Если все три метода не сработали — возвращается None,
    и вызывающий код использует старое резервное позиционирование.

    Args:
        page: страница PyMuPDF.
        grid_lines: (xs, ys) — координаты линий сетки от _get_cell_lines().
        table_bboxes: список bounding box'ов таблиц страницы
                      (используется как резервный источник границ колонок,
                      если линии сетки не распознаны).

    Returns:
        (x0, x1) — левая и правая граница колонки «Подпись», либо None,
        если колонку не удалось определить ни одним из методов.
    """
    # Собираем кандидаты границ колонок: линии сетки (приоритет), иначе —
    # границы таблиц find_tables (могут дать хотя бы внешний прямоугольник)
    xs: list[float] = []
    source = "сетка"
    if grid_lines:
        # Устойчивость к формату источника границ: ожидаем пару линий
        # (xs, ys); допускается также список bounding box'ов таблиц
        # (fitz.Rect) — границы колонок извлекаются из x0/x1.
        # Защита от ValueError "not enough values to unpack".
        if isinstance(grid_lines[0], fitz.Rect):
            edge_xs = sorted({float(v) for tb in grid_lines
                              for v in (tb.x0, tb.x1)})
            if len(edge_xs) >= 2:
                xs = edge_xs
                source = "границы таблиц"
        elif (len(grid_lines) >= 2
              and isinstance(grid_lines[0], (list, tuple))
              and len(grid_lines[0]) >= 2):
            xs = sorted(set(grid_lines[0]))
    if not xs and table_bboxes:
        edge_xs_set: set[float] = set()
        for tb in table_bboxes:
            edge_xs_set.add(float(tb.x0))
            edge_xs_set.add(float(tb.x1))
        xs = sorted(edge_xs_set)
        source = "границы таблиц"
    if len(xs) < 2:
        logger.debug("Колонка «Подпись»: нет линий сетки/таблиц для границ")
        return None

    # --- Метод 1: заголовок «Подпись» (канонический) ---
    result = _find_signature_column_x_by_header(page, xs, source)
    if result is not None:
        return result

    # --- Метод 2: эвристика «колонка слева от даты» ---
    logger.debug("Колонка «Подпись»: заголовок не найден — "
                 "эвристика по датам XX.XX")
    result = _find_sig_column_by_date(page, xs, page.rect.height)
    if result is not None:
        return result

    # --- Метод 3: fallback «предпоследняя колонка таблицы» ---
    logger.debug("Колонка «Подпись»: даты не найдены — "
                 "fallback по правой границе таблицы")
    result = _find_sig_column_by_fallback(table_bboxes, xs)
    if result is not None:
        return result

    logger.warning("Колонка 'Подпись' не найдена ни одним методом "
                   "(заголовок / дата / fallback) — используется "
                   "резервное позиционирование «справа от фамилии»")
    return None


def _cell_right_boundary(rect: fitz.Rect, cell: fitz.Rect,
                         grid_lines: Optional[tuple[list[float], list[float]]],
                         sig_col_x: Optional[tuple[float, float]] = None,
                         ) -> float:
    """Возвращает X-координату ПРАВОЙ ГРАНИЦЫ ячейки с фамилией — точку,
    от которой ставится подпись (резервное позиционирование, когда колонка
    «Подпись» по заголовку не найдена).

    Если известна колонка «Подпись» (sig_col_x) — возвращается её ЛЕВАЯ
    граница: подпись должна попадать именно в эту колонку, а не в соседнюю
    с фамилией служебную колонку «№ док.».

    Иначе берутся ВСЕ вертикальные линии сетки внутри bounding box ячейки
    правее текста фамилии. Фамилия может находиться в ОБЪЕДИНЁННОЙ ячейке
    (например, охватывает колонки «Лист» и «№ док.») — тогда ближайшая
    линия оказывается внутренней (фантомной) границей этой ячейки, и нужно
    взять ВТОРУЮ линию, пропуская её. Если внутренняя линия всего одна или
    их нет — используется первая подходящая / правый край ячейки."""
    # Приоритет: колонка «Подпись», найденная по заголовку
    if sig_col_x is not None:
        return sig_col_x[0]

    if grid_lines:
        # Устойчивость к формату: линии сетки (xs, ys); список Rect — bbox'ы
        xs = grid_lines[0] if not isinstance(grid_lines[0], fitz.Rect) else None
        if xs is None:
            xs = sorted({float(v) for tb in grid_lines for v in (tb.x0, tb.x1)})
        candidates = sorted(x for x in xs
                            if cell.x0 - 0.5 <= x <= cell.x1 + 0.5
                            and x >= rect.x1 - 0.5)
        if len(candidates) >= 2:
            # Берём вторую линию — пропускаем внутреннюю границу
            # объединённой ячейки с фамилией
            return candidates[1]
        if candidates:
            return candidates[0]
    return cell.x1


def _merge_line_group(rect: fitz.Rect, rects: list[fitz.Rect],
                      cell: Optional[fitz.Rect] = None) -> fitz.Rect:
    """Объединяет Rect вхождения с соседними строками ТЕКСТА той же ячейки.

    Инициалы и фамилия в одной ячейке могут быть набраны двумя строками —
    такие строки сливаются в один блок, чтобы подпись ставилась справа от
    всего блока. Строки из ДРУГИХ ячеек/СТРОК таблицы отсекаются:
      * если известна граница ячейки (cell.x1) — кандидаты, чей текст
        начинается правее неё, не присоединяются вовсе;
      * вертикальный зазор больше MAX_LINE_GAP_WITHIN_CELL_PT — это уже
        соседняя СТРОКА штампа (например, «Проверил» под «Разработал»),
        её вхождение фамилии обрабатывается отдельно;
      * требование сильного горизонтального пересечения
        (>= LINE_MERGE_X_OVERLAP_RATIO меньшей ширины).
    """
    group = [rect]
    changed = True
    while changed:
        changed = False
        for other in rects:
            if any(other is g for g in group):
                continue
            # candidate из соседней ячейки справа — не объединять
            if cell is not None and other.x0 > cell.x1 - 1.0:
                continue
            for g in group:
                gap = max(other.y0 - g.y1, g.y0 - other.y1)
                if gap > MAX_LINE_GAP_WITHIN_CELL_PT:
                    continue
                ov = min(other.x1, g.x1) - max(other.x0, g.x0)
                base = min(other.width, g.width)
                if base <= 0 or ov < LINE_MERGE_X_OVERLAP_RATIO * base:
                    continue
                group.append(other)
                changed = True
                break
    union = fitz.Rect(group[0])
    for g in group[1:]:
        union |= g
    return union


def _compute_insert_rect(rect: fitz.Rect, cell_right: Optional[float],
                         page_width: float, page_height: float,
                         cell_bottom: Optional[float] = None,
                         cell_top: Optional[float] = None,
                         target_cell: Optional[fitz.Rect] = None
                         ) -> fitz.Rect:
    """Вычисляет прямоугольник вставки подписи для вхождения фамилии.

    Горизонтальное позиционирование (новое требуемое поведение):
      Подпись ставится СТРОГО В SIGNATURE_GAP_FROM_NAME_MM (5 мм) СПРАВА ОТ
      ПРАВОГО КРАЯ ТЕКСТА фамилии: x0 = rect.x1 + SIGNATURE_GAP_FROM_NAME_PT.
      Это главный якорь по горизонтали. Центрирование по распознанной ячейке
      «Подпись» (target_cell) допускается только как корректировка: если центр ячейки
      находится в пределах MAX_SIG_CELL_DEV_MM (3 мм) от точки «фамилия+5 мм»,
      подпись центрируется по ячейке (она всё равно окажется рядом с фамилией);
      иначе геометрия ячейки игнорируется (ячейка распознана неверно или
      охватывает несколько колонок — из-за этого подписи и «убегали» слишком
      далеко от фамилии). Резервные варианты cell_right + OFFSET_RIGHT_PT и
      конец текста + NAME_GAP_MIN_PT сохранены для обратной совместимости,
      когда блок фамилии недоступен.

    Вертикальное позиционирование:
      Якорь — центр блока фамилии (rect); подпись центрируется напротив своей
      строки и ограничивается (clamp) пределами строки/целевой ячейки, если
      они заданы и не противоречат якорю (Сбой 2 — уход вверх).

    Args:
        rect: bounding box блока фамилии (главный якорь позиционирования).
        cell_right: X правой границы ячейки с фамилией (резервный вариант).
        page_width, page_height: размеры страницы.
        cell_bottom, cell_top: границы строки таблицы (резервный вариант).
        target_cell: целевая ячейка колонки «Подпись» (центрирование только
            вблизи якоря «фамилия + 5 мм»).

    Returns:
        fitz.Rect для вставки; пустой Rect, если место выходит за правый
        край страницы (вызывающий код пропустит его с предупреждением).
    """
    # ЭВРИСТИЧЕСКАЯ ЗАЩИТА ОТ «ПЕРЕВЁРНУТЫХ» СЛОЕВ (Сбой: подписи выходили
    # перевёрнутыми на 90° прямо поверх фамилии).
    # Если в PDF есть слой, повёрнутый на 90°, PyMuPDF может вернуть блок
    # текста с «переставленными» осями: очень узкий по X и высокий по Y.
    # Нормальная строка фамилии широкая и низкая; перевёрнутый блок — наоборот.
    # В таком случае считаем, что горизонталь/вертикаль перепутаны местами,
    # и меняем их, чтобы якорь «правый край фамилии + 5 мм» считался по
    # фактическому направлению чтения текста, а не по оси слоя.
    if (rect is not None and not rect.is_empty and rect.width > 0
            and rect.height > 0 and rect.height > rect.width * 2.0):
        logger.warning("Блок фамилии имеет признаки перевёрнутого слоя "
                       "(высота %.1f pt >> ширина %.1f pt) — оси нормализованы",
                       rect.height, rect.width)
        rect = fitz.Rect(rect.y0, rect.x0, rect.y1, rect.x1)

    w = SIGNATURE_WIDTH_PT
    h = SIGNATURE_HEIGHT_PT

    valid_name_block = (rect is not None and not rect.is_empty
                        and rect.width > 0 and rect.height > 0)

    # --- Горизонталь: главный якорь — «правый край фамилии + 5 мм» ------
    used_method = "gap_from_name"
    if valid_name_block:
        x0 = rect.x1 + SIGNATURE_GAP_FROM_NAME_PT
    elif target_cell is not None and not target_cell.is_empty:
        # Обратная совместимость: блок фамилии недоступен — центрируем
        # по ячейке «Подпись» (старое поведение варианта 1)
        x0 = target_cell.x0 + (target_cell.width - w) / 2.0
        used_method = "sig_cell_centered_no_block"
    elif cell_right is not None:
        x0 = cell_right + OFFSET_RIGHT_PT
        used_method = "cell_right"
    else:
        x0 = page_width - w - OFFSET_RIGHT_PT
        used_method = "page_edge"

    # Требование: подпись стоит в 5 мм СПРАВА ОТ ФАМИЛИИ — центрирование
    # по ячейке «Подпись» НЕ применяется, если из-за этого подпись убегает
    # далеко от фамилии. Если же ячейка расположена вплотную к фамилии
    # (её центр в пределах MAX_SIG_CELL_DEV_MM от точки «фамилия+5 мм»),
    # оставляем аккуратное центрирование по ячейке.
    if valid_name_block and target_cell is not None and not target_cell.is_empty:
        gap_x0 = rect.x1 + SIGNATURE_GAP_FROM_NAME_PT
        cell_center_x = target_cell.x0 + target_cell.width / 2.0
        name_center_target = gap_x0 + w / 2.0
        if abs(cell_center_x - name_center_target) <= MAX_SIG_CELL_DEV_PT:
            x0 = target_cell.x0 + (target_cell.width - w) / 2.0
            used_method = "sig_cell_centered"
    logger.debug("Горизонтальный якорь подписи: метод=%s, "
                 "x_конец_фамилии=%.1f, x0_подписи=%.1f (зазор %.1f pt "
                 "= %.2f мм)", used_method,
                 rect.x1 if valid_name_block else float('nan'), x0,
                 (x0 - rect.x1) if valid_name_block else float('nan'),
                 ((x0 - rect.x1) / MM_TO_PT) if valid_name_block else float('nan'))

    # --- Вертикаль: якорь — центр строки фамилии ------------------------
    anchor_y = ((rect.y0 + rect.y1) / 2.0 if valid_name_block
                else (target_cell.y0 + target_cell.y1) / 2.0
                if target_cell is not None and not target_cell.is_empty
                else (cell_top + cell_bottom) / 2.0
                if cell_top is not None and cell_bottom is not None
                else 0.0)
    y0 = anchor_y - h / 2.0

    # Clamp в пределах целевой ячейки/полосы строки — ТОЛЬКО когда блок
    # фамилии недоступен. Если блок валиден, подпись обязана стоять ровно
    # напротив своей строки (центр подписи = центр блока): clamp по полосе,
    # охватывающей несколько строк из-за неточного распознавания линий,
    # уводил подпись вверх/вниз относительно фамилии.
    def _clamp_ok(band_top: float, band_bottom: float) -> bool:
        return (band_bottom > band_top
                and band_top - 1.0 <= anchor_y <= band_bottom + 1.0)

    if not valid_name_block:
        if (target_cell is not None and not target_cell.is_empty
                and _clamp_ok(target_cell.y0, target_cell.y1)):
            band_h = target_cell.y1 - target_cell.y0
            if band_h >= h:
                y0 = max(target_cell.y0, min(y0, target_cell.y1 - h))
        elif cell_top is not None and cell_bottom is not None \
                and _clamp_ok(cell_top, cell_bottom):
            if cell_bottom - cell_top >= h:
                y0 = max(cell_top, min(y0, cell_bottom - h))

    # не выходим за края страницы
    if y0 < 0:
        y0 = 0.0
    if y0 + h > page_height:
        y0 = max(page_height - h, 0.0)

    target = fitz.Rect(x0, y0, x0 + w, y0 + h)
    if target.x1 > page_width:
        return fitz.Rect(0, 0, 0, 0)  # помечен как невалидный
    return target


def is_rect_in_stamp(page: fitz.Page, rect: fitz.Rect,
                     table_bboxes: Optional[list[fitz.Rect]]) -> bool:
    """Фильтр «вхождение внутри штампа» (Шаг B).

    Приоритет проверок:
      1. Если фамилия внутри таблицы (table_bboxes) — сразу возвращаем True
         (фильтры зон не применяются, так как таблица уже гарантирует
         принадлежность к штампу). Это исправляет пропуск фамилий в верхних
         строках штампа на страницах, где штамп начинается выше порога
         нижней зоны (например, из-за дополнительных пустых строк таблицы
         над штампом).
      2. Иначе — проверяем фильтры нижней/правой зоны (с допуском
         STAMP_ZONE_TOLERANCE_PT и оператором >=) + fallback по словам:
         а) Нижняя зона страницы: rect.y0 >= STAMP_ZONE_BOTTOM_RATIO *
            page_height - допуск.
         б) Правая зона страницы: rect.x0 >= STAMP_ZONE_RIGHT_RATIO *
            page_width - допуск (доля снижена до 0.20 — фамилия во второй
            колонке штампа может находиться левее 40% ширины листа).
         в) Fallback: рядом с rect присутствует хотя бы одно слово из
            STAMP_NEIGHBOR_WORDS («Разработал», «Проверил», «ГИП»,
            «Н.контр.» и варианты написания).

    Args:
        page: страница PyMuPDF.
        rect: bounding box найденного вхождения фамилии.
        table_bboxes: список bounding box'ов таблиц страницы
                      (None — find_tables недоступен).

    Returns:
        True, если вхождение признано частью ГОСТ-штампа.
    """
    page_width = page.rect.width
    page_height = page.rect.height

    # Приоритет 1: попадание в таблицу — главный критерий.
    # Фамилия внутри распознанной таблицы гарантированно часть штампа,
    # поэтому фильтры зон к ней не применяются.
    if table_bboxes and _is_inside_any_table(rect, table_bboxes):
        return True

    # Приоритет 2: фильтры зон (только если не внутри таблицы)
    tol = STAMP_ZONE_TOLERANCE_PT

    # 1. Нижняя зона страницы (с допуском)
    if rect.y0 < STAMP_ZONE_BOTTOM_RATIO * page_height - tol:
        return False
    # 2. Правая зона страницы (с допуском)
    if rect.x0 < STAMP_ZONE_RIGHT_RATIO * page_width - tol:
        return False
    # 3. Резервная проверка соседними словами штампа (find_tables может
    #    не распознать штамп как таблицу целиком)
    logger.debug("Вхождение (%.1f; %.1f) не попало в таблицы — "
                 "fallback по соседним словам", rect.x0, rect.y0)
    return _has_stamp_neighbor_word(page, rect)


def find_stamp_cells(
    page: fitz.Page,
    surnames: Optional[dict] = None,
) -> dict:
    """Автоматически находит позиции вставки подписей на странице PDF.

    Шаг A — поиск всех вхождений фамилий:
        Для каждой фамилии из SIGNER_BY_SURNAME выполняется
        page.search_for("фамилия"); собирается список кандидатов
        [(rect, signer_id), ...].

    Шаг B — фильтрация «внутри штампа»:
        Каждое вхождение проверяется is_rect_in_stamp(): нижняя/правая
        зона страницы + попадание в таблицу (page.find_tables()) либо
        соседство со словами-ориентирами штампа. Упоминания фамилий
        в основном тексте отбрасываются.

    Шаг C — расчёт целевого прямоугольника:
        Картинка размещается СПРАВА от фамилии — в пустую ячейку колонки
        «Подпись» той же строки штампа (_find_signature_column_cell:
        соседняя справа ячейка, без текста, шириной >= 15 мм), где подпись
        центрируется по горизонтали и вертикали. Если сетка ячеек не
        распознана — резерв: правая граница ячейки + OFFSET_RIGHT_PT либо
        конец текста фамилии + NAME_GAP_MIN_PT. Каждое вхождение фамилии
        (даже повторяющееся в разных строках штампа) обрабатывается
        отдельно; дедупликация выполняется по самой ячейке с фамилией, а
        не по координатам вставки. Строки текста одной ячейки («И.О.» /
        «Фамилия») объединяются в блок. Прямоугольники, выходящие за край
        страницы, помечаются пустым Rect (вызывающий код пропустит их с
        предупреждением).

    Args:
        page: страница PyMuPDF.
        surnames: словарь {фамилия: id_подписанта}. По умолчанию
                  SIGNER_BY_SURNAME.

    Returns:
        Словарь:
          {"candidates": [
              {"surname": str, "signer_id": int, "name_rect": fitz.Rect,
               "target_rect": fitz.Rect}, ...],
           "found_surnames": set[str],   # фамилии, найденные где угодно
           "skipped_outside": [str,...], # найдены, но вне штампа
           "skip_reasons": [str,...],    # причины пропуска вхождений (диагностика)
          }

    Raises:
        StampNotFoundError: если ни одна фамилия не найдена на странице.
    """
    if surnames is None:
        surnames = SIGNER_BY_SURNAME

    page_rect = page.rect
    logger.info("Поиск фамилий штампа на странице (размер %.1f x %.1f pt)",
                page_rect.width, page_rect.height)

    # --- Шаг A: собираем кандидатов -------------------------------
    candidates: list[dict] = []
    found_surnames: set[str] = set()
    skipped_outside: list[str] = []
    skip_reasons: list[str] = []   # диагностика причин пропуска вставок

    # Таблицы страницы находим один раз (используются для всех кандидатов)
    table_bboxes = _get_page_tables_bboxes(page)
    # Линии сетки штампа — один раз на страницу (нужны даже при наличии
    # find_tables: bounding box таблицы не даёт границ отдельных ячеек)
    grid_lines = _get_cell_lines(page)

    # Колонка «Подпись» ищется ПО ЗАГОЛОВКУ в шапке штампа — один раз на
    # страницу. Это надёжнее «ближайшей линии справа от фамилии»: фамилия
    # может занимать объединённую ячейку («Лист» + «№ док.»), и подпись
    # должна попадать через одну ячейку правее — в настоящую колонку
    # «Подпись», а не в служебную «№ док.»
    sig_col_x = _find_signature_column_x(page, grid_lines, table_bboxes)
    # Устойчивость к формату возврата: нормализуем результат к паре
    # (x0, x1). Любая неожиданная структура (строка, короткий/длинный
    # список) не должна приводить к ValueError при распаковке у вызова
    # _find_signature_column_cell / _cell_right_boundary.
    if sig_col_x is not None:
        try:
            vals = [float(v) for v in sig_col_x]
        except (TypeError, ValueError):
            logger.warning("Некорректный формат колонки «Подпись»: %r — "
                           "переход к резервному позиционированию",
                           sig_col_x)
            vals = []
        if len(vals) >= 2 and vals[1] > vals[0]:
            if len(vals) > 2:
                logger.debug("Колонка «Подпись»: получено %d значений — "
                             "используются первые два", len(vals))
            sig_col_x = (vals[0], vals[1])
        else:
            sig_col_x = None
    if sig_col_x is not None:
        # Диагностика (требование 7): метод определения колонки и координаты
        logger.info("Колонка «Подпись» на странице: x=[%.1f; %.1f] "
                    "(ширина %.1f pt)", sig_col_x[0], sig_col_x[1],
                    sig_col_x[1] - sig_col_x[0])
    else:
        logger.warning("Колонка 'Подпись' не найдена (заголовок / дата / "
                       "fallback) — используется резервное позиционирование "
                       "по сетке «справа от фамилии»")

    for surname, signer_id in surnames.items():
        rects = page.search_for(surname)
        if not rects:
            logger.debug("Фамилия '%s' на странице не найдена", surname)
            continue
        found_surnames.add(surname)
        logger.info("Фамилия '%s' найдена: %d вход.", surname, len(rects))

        in_stamp_count = 0
        # Дедупликация «ФАМИЛИЯ + СТРОКА ячейки» (а не по координатам
        # вставки): две разные строки штампа с одной фамилией («Проверил»
        # и «Гл.констр.» — обе «Лисицын») дают РАЗНЫЕ строки -> подпись
        # ставится у каждой; вторая строка текста той же ячейки («И.О.»
        # над «Фамилией») даёт ту же строку -> пропускается. Округление
        # Y до целого пункта защищает от ложных дубликатов при разбросе
        # координат на доли пункта между страницами.
        processed: set[tuple[str, int]] = set()
        for rect in rects:
            # --- Шаг B: фильтр «внутри штампа» ---
            if not is_rect_in_stamp(page, rect, table_bboxes):
                logger.info("'%s' в (%.1f; %.1f) — вне штампа, пропущено",
                            surname, rect.x0, rect.y0)
                continue
            in_stamp_count += 1

            # --- Шаг C: целевой прямоугольник справа от фамилии ---
            # Границы ячейки с фамилией: сначала по линиям сетки
            # (find_tables cells / get_drawings), затем резерв — bbox таблицы
            cell = None
            if grid_lines:
                cell = _find_containing_cell(rect, grid_lines)
            if cell is None and table_bboxes:
                cell = _find_containing_cell(rect, table_bboxes)

            # Ключ дедупликации: фамилия + Y-координата верха СТРОКИ ячейки
            key_y = cell.y0 if cell is not None else rect.y0
            key = (surname, round(key_y))
            if key in processed:
                # Это вхождение — вторая строка уже обработанного блока
                # той же ячейки
                logger.debug("'%s': дубликат в строке y=%.1f — пропуск",
                             surname, key_y)
                continue
            processed.add(key)

            # Диагностика: координаты блока текста и найденной ячейки
            if cell is not None:
                logger.info("'%s' (стр. y=%.0f): текст (%.1f; %.1f)-(%.1f; "
                            "%.1f), ячейка (%.1f; %.1f)-(%.1f; %.1f)",
                            surname, key_y, rect.x0, rect.y0, rect.x1,
                            rect.y1, cell.x0, cell.y0, cell.x1, cell.y1)
            else:
                logger.info("'%s' (стр. y=%.0f): текст (%.1f; %.1f)-(%.1f; "
                            "%.1f), ячейка не распознана",
                            surname, key_y, rect.x0, rect.y0, rect.x1,
                            rect.y1)

            # Объединяем строки текста одной ячейки («И.О.» / «Фамилия»).
            # Кандидаты на объединение ограничены горизонтальными границами
            # СТРОКИ данного вхождения: иначе соседние строки штампа с той же
            # фамилией («Проверил» и «Гл.констр.» — оба «Лисицын») сливаются
            # в один блок, и обе подписи встают в одну строку (дубликат).
            # Если линии строки не распознаны — резерв по границам ячейки
            row_t0, row_b0 = _row_bounds(rect, grid_lines, cell)
            row_rects = [r for r in rects
                         if r.y0 >= row_t0 - 1.0
                         and r.y1 <= row_b0 + 1.0]
            block = _merge_line_group(rect, row_rects, cell)

            # Правая граница ячейки может сузиться после объединения строк.
            # Если колонка «Подпись» найдена по заголовку — используется она
            # (подпись НЕ должна попадать в служебную колонку «№ док.»)
            cell_right = (_cell_right_boundary(block, cell, grid_lines,
                                               sig_col_x)
                          if cell is not None else None)

            # Целевая ячейка колонки «Подпись»: сначала по заголовку колонки
            # (sig_col_x), затем резерв — соседняя справа по сетке; та же
            # строка, пустая — подпись центрируется внутри неё
            target_cell: Optional[fitz.Rect] = None
            if cell is not None or sig_col_x is not None or grid_lines:
                target_cell, reason = _find_signature_column_cell(
                    page, block, cell if cell is not None else block,
                    grid_lines, sig_col_x, rect)
                if target_cell is not None:
                    logger.info("'%s' (стр. ячейки y=%.1f): целевая ячейка "
                                "«Подпись» (%.1f; %.1f)-(%.1f; %.1f)",
                                surname, key_y, target_cell.x0,
                                target_cell.y0, target_cell.x1,
                                target_cell.y1)
                else:
                    msg = (f"'{surname}' ({rect.x0:.1f}; {rect.y0:.1f}): "
                           f"ячейка «Подпись» не найдена ({reason}) — "
                           f"резервное позиционирование")
                    logger.info(msg)
                    skip_reasons.append(msg)

            # Точные границы СТРОКИ ячейки (по горизонтальным линиям сетки
            # вокруг блока; резерв — границы ячейки/блока), а не всего
            # bounding box'а таблицы: иначе все подписи встали бы на уровне
            # последней строки штампа
            row_top, row_bottom = _row_bounds(block, grid_lines, cell)
            # Диагностика (требование 7): координаты строки фамилии и
            # целевой ячейки для каждой вставки
            logger.info("'%s' (стр. y=%.1f): строка фамилии y=[%.1f; %.1f], "
                        "блок текста y=[%.1f; %.1f], целевая ячейка %s",
                        surname, key_y,
                        row_top if row_top is not None else -1.0,
                        row_bottom if row_bottom is not None else -1.0,
                        block.y0, block.y1,
                        ("(%.1f; %.1f)-(%.1f; %.1f)" %
                         (target_cell.x0, target_cell.y0,
                          target_cell.x1, target_cell.y1))
                        if target_cell is not None else "не найдена")

            target = _compute_insert_rect(block, cell_right,
                                          page_rect.width, page_rect.height,
                                          cell_bottom=row_bottom,
                                          cell_top=row_top,
                                          target_cell=target_cell)
            if target.is_empty:
                msg = (f"'{surname}' (стр. y={key_y:.0f}): позиция вставки "
                       f"выходит за правый край страницы — пропуск")
                logger.warning(msg)
                skip_reasons.append(msg)
                continue

            # Диагностика: итоговые координаты вставки относительно строки
            # фамилии (смещение центра подписи от центра блока ~ 0 подтверждает,
            # что подпись стоит строго напротив своей строки)
            logger.info("'%s' (стр. y=%.0f): позиция вставки "
                        "(%.1f; %.1f)-(%.1f; %.1f), центр подписи y=%.1f, "
                        "центр фамилии y=%.1f",
                        surname, key_y, target.x0, target.y0,
                        target.x1, target.y1,
                        (target.y0 + target.y1) / 2.0,
                        (block.y0 + block.y1) / 2.0)

            candidates.append({
                "surname": surname,
                "signer_id": signer_id,
                "name_rect": block,
                "target_rect": target,
            })

        if in_stamp_count == 0:
            skipped_outside.append(surname)

    if not found_surnames:
        raise StampNotFoundError(
            "Штамп не распознан: фамилии "
            f"{', '.join(repr(s) for s in surnames)} отсутствуют на странице. "
            "Укажите координаты вручную или проверьте PDF."
        )

    logger.info("Итого валидных позиций в штампе: %d "
                "(фамилии вне штампа: %s)",
                len(candidates), skipped_outside or "нет")
    return {
        "candidates": candidates,
        "found_surnames": found_surnames,
        "skipped_outside": skipped_outside,
        "skip_reasons": skip_reasons,
    }


# ============================================================================
# ЛОГИКА: парсинг списка страниц
# ============================================================================

def parse_pages(page_string):
    """Парсит строку вида "1,10-16,21" и возвращает отсортированный список
    уникальных номеров страниц.

    Правила:
      * Пустая строка возвращает None — признак «все страницы документа».
      * Элементы разделяются запятыми.
      * Элемент вида "10-16" — диапазон (включительно) [10..16].
      * Элемент вида "1" — одиночная страница [1].

    Исключения:
      ValueError — при некорректном формате ("abc", "10-5", пустые элементы и т.п.)
    """
    if page_string is None or not str(page_string).strip():
        # Пустой список допустим: означает «обработать все страницы»
        return None

    pages = set()

    for part in str(page_string).split(","):
        part = part.strip()
        if not part:
            raise ValueError("Пустой элемент в списке страниц. "
                             "Пример формата: 1,10-16,21")

        if "-" in part:
            # Диапазон страниц, например "10-16"
            bounds = part.split("-")
            if len(bounds) != 2:
                raise ValueError(
                    f"Некорректный диапазон '{part}'. "
                    f"Ожидается формат 'начало-конец', например '10-16'."
                )
            start_str, end_str = (b.strip() for b in bounds)
            try:
                start = int(start_str)
                end = int(end_str)
            except ValueError:
                raise ValueError(
                    f"Не удалось распознать диапазон '{part}': "
                    f"границы должны быть целыми числами."
                )
            if start > end:
                raise ValueError(
                    f"Некорректный диапазон '{part}': начальная страница "
                    f"({start}) больше конечной ({end})."
                )
            if start < 1:
                raise ValueError(
                    f"Некорректный диапазон '{part}': номера страниц "
                    f"должны начинаться с 1."
                )
            pages.update(range(start, end + 1))
        else:
            # Одиночная страница, например "1" или "21"
            try:
                num = int(part)
            except ValueError:
                raise ValueError(
                    f"Не удалось распознать страницу '{part}': "
                    f"ожидается целое число или диапазон вида '10-16'."
                )
            if num < 1:
                raise ValueError(
                    f"Некорректный номер страницы '{num}': "
                    f"номера страниц должны начинаться с 1."
                )
            pages.add(num)

    return sorted(pages)


# ============================================================================
# ЛОГИКА: поиск PNG-файлов в папках подписей
# ============================================================================

def find_png_files(folder):
    """Возвращает список всех PNG-файлов в указанной папке (без учёта регистра)."""
    if not folder or not os.path.isdir(folder):
        raise FileNotFoundError(f"Папка не найдена: {folder}")
    pngs = glob.glob(os.path.join(folder, "*.png")) + \
           glob.glob(os.path.join(folder, "*.PNG"))
    # Убираем возможные дубликаты (для файловых систем без учёта регистра)
    return sorted(set(os.path.abspath(p) for p in pngs))


# ============================================================================
# ЛОГИКА: вставка подписей в PDF
# ============================================================================

def _insert_signature_image(page, rect: fitz.Rect, png_path: str) -> None:
    """Вставляет PNG-подпись в прямоугольник rect СТРОГО ГОРИЗОНТАЛЬНО.

    Проблема (Сбой «подписи перевёрнуты на 90°»): page.insert_image() без
    явного transform наследует ориентацию CTM страницы/слоя. Если страница
    повёрнута (page.rotation != 0), картинка может быть нарисована
    повёрнутой на 90°.

    Решение: PyMuPDF 1.28 сам корректно позиционирует растровые изображения
    на повёрнутых страницах (rotation учитывается при расчёте матрицы
    вставки). Дополнительно используем параметр rotate=0, явно фиксируя
    ГОРИЗОНТАЛЬНУЮ ориентацию картинки относительно наблюдателя; для
    старых версий PyMuPDF (где rotate задаёт сетку 90°) это тоже безопасный
    дефолт. Pixmap-вариант — резерв при недоступности filename.
    """
    rotation = getattr(page, "rotation", 0) or 0
    try:
        # rotate=0 => горизонтальная ориентация подписи (компенсация
        # поворота страницы выполняется самим PyMuPDF при рендере)
        page.insert_image(rect, filename=png_path, rotate=0)
    except Exception as exc:
        logger.warning("Стандартная вставка не удалась (%s) — pixmap-резерв",
                       exc)
        pix = fitz.Pixmap(png_path)
        page.insert_image(rect, pixmap=pix, rotate=0)
    if rotation % 360 != 0:
        logger.info("Страница повёрнута (rotation=%d) — подпись вставлена "
                    "горизонтально (rotate=0) в rect (%.1f; %.1f)-(%.1f; %.1f)",
                    rotation, rect.x0, rect.y0, rect.x1, rect.y1)


def _insert_manual_mode(page, page_width, page_height, signer1_pngs,
                        signer2_pngs, log_func):
    """РУЧНОЙ РЕЖИМ (fallback): вставка 4 подписей по фиксированным отступам
    страницы. Используется при включённом чекбоксе «Ручной режим» или если
    штамп не распознан.

    Args:
        page: страница PyMuPDF.
        page_width, page_height: размеры страницы в пунктах.
        signer1_pngs, signer2_pngs: списки путей PNG-файлов подписантов.
        log_func: функция вывода сообщений в лог GUI.
    """
    for slot_index, (signer_id, bottom_margin_pt) in enumerate(
            SIGNATURE_SLOTS, start=1):
        # Выбор случайного PNG нужного подписанта (на каждое место каждой
        # страницы — заново)
        pool = signer1_pngs if signer_id == 1 else signer2_pngs
        chosen_png = random.choice(pool)

        # Расчёт координат верхнего левого угла прямоугольника вставки
        # (PyMuPDF считает координаты от верхнего левого угла страницы)
        x = page_width - RIGHT_MARGIN_PT - SIGNATURE_WIDTH_PT
        y = page_height - bottom_margin_pt - SIGNATURE_HEIGHT_PT

        rect = fitz.Rect(x, y,
                         x + SIGNATURE_WIDTH_PT,
                         y + SIGNATURE_HEIGHT_PT)

        _insert_signature_image(page, rect, chosen_png)
        log_func(f"  [ручной режим] Место №{slot_index}: Подписант {signer_id}, "
                 f"отступ снизу {bottom_margin_pt} pt, "
                 f"координаты ({x:.1f}; {y:.1f}), "
                 f"файл: {os.path.basename(chosen_png)}")


def process_pdf(pdf_path, page_numbers, signer1_pngs, signer2_pngs, log_func,
                manual_mode: bool = False):
    """Вставляет подписи на указанные страницы PDF-файла и перезаписывает его.

    По умолчанию используется АВТООПРЕДЕЛЕНИЕ (find_stamp_cells): на странице
    ищутся фамилии из SIGNER_BY_SURNAME; подпись ставится справа от каждой
    фамилии, найденной внутри ГОСТ-штампа (упоминания в тексте игнорируются).
    Если ни одна фамилия не найдена — страница пропускается с записью в лог.
    При включённом чекбоксе «Ручной режим» работает старая логика —
    4 подписи по фиксированным отступам страницы (_insert_manual_mode).

    Параметры:
        pdf_path      — путь к PDF-файлу;
        page_numbers  — список номеров страниц (начиная с 1);
                      если None — обрабатываются ВСЕ страницы документа;
        signer1_pngs  — список путей PNG-файлов Подписанта 1;
        signer2_pngs  — список путей PNG-файлов Подписанта 2;
        log_func      — функция для вывода сообщений в лог GUI;
        manual_mode   — принудительно использовать ручный режим вставки.
    """
    doc = fitz.open(pdf_path)
    try:
        total_pages = doc.page_count

        # Если страницы не указаны — обрабатываем весь документ
        if page_numbers is None:
            page_numbers = list(range(1, total_pages + 1))

        # Проверка существования указанных страниц
        invalid = [p for p in page_numbers if p > total_pages]
        if invalid:
            raise ValueError(
                f"В PDF только {total_pages} стр. "
                f"Указанные страницы не существуют: {invalid}"
            )

        for page_num in page_numbers:
            # Нумерация в UI с 1, в PyMuPDF с 0
            page = doc[page_num - 1]
            page_width = page.rect.width
            page_height = page.rect.height

            log_func(f"— Обработка страницы {page_num} "
                     f"(размер: {page_width:.1f} x {page_height:.1f} pt)")

            # --- Ручной режим (fallback): старая логика без изменений ---
            if manual_mode:
                _insert_manual_mode(page, page_width, page_height,
                                    signer1_pngs, signer2_pngs, log_func)
                continue

            # --- Автоопределение: поиск фамилий внутри штампа ---
            try:
                result = find_stamp_cells(page)
            except StampNotFoundError as e:
                logger.warning("Страница %d: %s", page_num, e)
                log_func(f"  Стр. {page_num}: штамп не найден — "
                         f"страница пропущена ({e})")
                continue

            candidates = result["candidates"]

            # Фамилии найдены, но все вхождения — вне штампа
            if not candidates:
                outside = ", ".join(result["skipped_outside"])
                log_func(f"  Стр. {page_num}: фамилии ({outside}) найдены, "
                         f"но вне штампа — страница пропущена")
                logger.info("Страница %d: все вхождения отфильтрованы "
                            "как «вне штампа»", page_num)
                continue

            # Диагностика: причины, по которым вставки не выполнялись
            for reason in result.get("skip_reasons", []):
                log_func(f"  Стр. {page_num}: {reason}")

            # Вставка: случайный PNG выбирается заново для КАЖДОГО вхождения
            for cand in candidates:
                surname = cand["surname"]
                signer_id = cand["signer_id"]
                target = cand["target_rect"]

                if target.is_empty:
                    log_func(f"  Стр. {page_num}: '{surname}' в штампе, но "
                             f"место справа от фамилии выходит за край "
                             f"страницы — ПРОПУСК с предупреждением")
                    logger.warning("Страница %d: целевой rect для '%s' "
                                   "выходит за край страницы", page_num,
                                   surname)
                    continue

                pool = signer1_pngs if signer_id == 1 else signer2_pngs
                chosen_png = random.choice(pool)

                _insert_signature_image(page, target, chosen_png)
                log_func(
                    f"  Стр. {page_num}: найдена фамилия '{surname}' "
                    f"в штампе → Подписант {signer_id}, "
                    f"координаты ({target.x0:.1f}; {target.y0:.1f})-"
                    f"({target.x1:.1f}; {target.y1:.1f}), "
                    f"файл: {os.path.basename(chosen_png)}"
                )
                logger.info("Страница %d: вставка у '%s' (%.1f; %.1f), файл %s",
                            page_num, surname, target.x0, target.y0,
                            os.path.basename(chosen_png))

            # Логируем фамилии, найденные только вне штампа (в тексте)
            for surname in result["skipped_outside"]:
                log_func(f"  Стр. {page_num}: '{surname}' найден, "
                         f"но вне штампа — пропущено")

        # Сохранение результата БЕЗ создания резервной копии.
        # PyMuPDF не умеет писать документ в тот же файл, из которого он
        # открыт, поэтому сохраняем во временный файл в той же папке,
        # а затем подменяем им оригинал — файл просто обрабатывается на месте.
        tmp_path = pdf_path + ".tmp_write"
        try:
            doc.ez_save(tmp_path)
            doc.close()
            doc = None
            os.replace(tmp_path, pdf_path)
        except Exception:
            # На случай ошибки записи удаляем неполный временный файл
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
            raise
        log_func(f"Файл сохранён (перезаписан): {pdf_path}")
    finally:
        if doc is not None:
            doc.close()


# ============================================================================
# GUI (tkinter)
# ============================================================================

class SignatureApp:
    """Главное окно приложения."""

    def __init__(self, root):
        self.root = root
        self.root.title("Вставка подписей в PDF")
        self.root.geometry("700x560")
        self.root.minsize(600, 480)

        # Переменные для хранения выбранных путей
        self.pdf_path = tk.StringVar()
        self.pages_str = tk.StringVar()
        self.signer1_folder = tk.StringVar()
        self.signer2_folder = tk.StringVar()

        # Чекбокс «Ручной режим» — fallback-вставка по фиксированным
        # координатам страницы вместо автоопределения ячеек штампа
        self.manual_mode = tk.BooleanVar(value=False)

        # Кэш найденных ячеек штампа {номер_страницы: {имя: fitz.Rect}}
        self._stamp_cells: dict[int, dict] = {}

        self._build_widgets()

    def _build_widgets(self):
        pad = {"padx": 10, "pady": 5}

        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill="both", expand=True, padx=10, pady=10)

        # --- PDF-файл ---
        row1 = ttk.Frame(main_frame)
        row1.pack(fill="x")
        ttk.Button(row1, text="Выбрать PDF файл",
                   command=self.choose_pdf).pack(side="left")
        ttk.Entry(row1, textvariable=self.pdf_path).pack(
            side="left", fill="x", expand=True, padx=(10, 0))

        # --- Страницы ---
        row2 = ttk.Frame(main_frame)
        row2.pack(fill="x", **pad)
        ttk.Label(row2, text="Страницы для обработки:").pack(side="left")
        ttk.Entry(row2, textvariable=self.pages_str).pack(
            side="left", fill="x", expand=True, padx=(10, 0))
        ttk.Label(main_frame,
                  text='Формат: "1,10-16,21". Оставьте пустым — обработаются '
                       'все страницы.',
                  foreground="gray").pack(anchor="w", padx=(0, 0))

        # Placeholder-подобная подсказка внутри поля ввода
        def show_placeholder(_):
            if not self.pages_str.get():
                self.pages_str.set("1,10-16,21")
        def hide_placeholder(_):
            if self.pages_str.get() == "1,10-16,21":
                self.pages_str.set("")
        entry_widget = row2.winfo_children()[1]
        entry_widget.bind("<FocusIn>", hide_placeholder)
        entry_widget.bind("<FocusOut>", show_placeholder)
        show_placeholder(None)

        # --- Папки подписантов ---
        row3 = ttk.Frame(main_frame)
        row3.pack(fill="x", **pad)
        ttk.Button(row3, text="Выбрать папку с подписями Подписанта 1",
                   command=self.choose_signer1_folder).pack(side="left")
        ttk.Entry(row3, textvariable=self.signer1_folder).pack(
            side="left", fill="x", expand=True, padx=(10, 0))

        row4 = ttk.Frame(main_frame)
        row4.pack(fill="x", **pad)
        ttk.Button(row4, text="Выбрать папку с подписями Подписанта 2",
                   command=self.choose_signer2_folder).pack(side="left")
        ttk.Entry(row4, textvariable=self.signer2_folder).pack(
            side="left", fill="x", expand=True, padx=(10, 0))

        # --- Кнопка обработки + чекбокс ручного режима (fallback) ---
        btn_row = ttk.Frame(main_frame)
        btn_row.pack(fill="x", **pad)
        self.process_btn = ttk.Button(btn_row, text="Обработать",
                                      command=self.on_process_clicked)
        self.process_btn.pack(side="left")
        ttk.Checkbutton(btn_row,
                        text="Ручной режим (вставка по фиксированным "
                             "координатам, без автопоиска штампа)",
                        variable=self.manual_mode).pack(side="left", padx=15)

        # --- Лог ---
        log_frame = ttk.LabelFrame(main_frame, text="Журнал")
        log_frame.pack(fill="both", expand=True)
        self.log_text = tk.Text(log_frame, height=12, wrap="word",
                                state="disabled", font=("Consolas", 9))
        log_scroll = ttk.Scrollbar(log_frame, command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=log_scroll.set)
        self.log_text.pack(side="left", fill="both", expand=True,
                           padx=(5, 0), pady=5)
        log_scroll.pack(side="right", fill="y", pady=5)

    # ---------- Диалоги выбора ----------

    def choose_pdf(self):
        path = filedialog.askopenfilename(
            title="Выберите PDF файл",
            filetypes=[("PDF файлы", "*.pdf"), ("Все файлы", "*.*")])
        if path:
            self.pdf_path.set(path)
            # Автоопределение ячеек штампа сразу после выбора PDF
            self.auto_detect_cells()

    def auto_detect_cells(self):
        """Запускает find_stamp_cells() для всех страниц выбранного PDF,
        кэширует найденные позиции вхождений фамилий и выводит результат
        в журнал (аналог превью: координаты Rect можно использовать для
        отрисовки красных прямоугольников).

        Если штамп не распознан ни на одной странице — показывает понятное
        сообщение и предлагает fallback: чекбокс «Ручной режим».
        """
        pdf_path = self.pdf_path.get().strip()
        if not pdf_path or not os.path.isfile(pdf_path):
            return

        self._stamp_cells = {}
        self.log("Автоопределение: поиск фамилий в штампе...")
        logger.info("Автоопределение позиций подписей: %s", pdf_path)

        try:
            doc = fitz.open(pdf_path)
        except Exception as e:
            self._show_error(f"Не удалось открыть PDF: {e}")
            return

        detected = 0
        failed_pages: list[int] = []
        try:
            for i in range(doc.page_count):
                page = doc[i]
                try:
                    result = find_stamp_cells(page)
                    candidates = result["candidates"]
                    if not candidates:
                        # Фамилии есть, но все вне штампа
                        self.log(f"  Стр. {i + 1}: фамилии найдены, "
                                 f"но вне штампа — пропущено")
                        failed_pages.append(i + 1)
                        continue
                    self._stamp_cells[i + 1] = candidates
                    detected += 1
                    # Вывод координат найденных позиций вставки
                    for cand in candidates:
                        rect = cand["target_rect"]
                        if rect.is_empty:
                            self.log(f"  Стр. {i + 1}: '{cand['surname']}' → "
                                     f"Подписант {cand['signer_id']}, "
                                     f"место выходит за край страницы")
                        else:
                            self.log(f"  Стр. {i + 1}: '{cand['surname']}' → "
                                     f"Подписант {cand['signer_id']}, "
                                     f"прямоугольник [{rect.x0:.1f}, "
                                     f"{rect.y0:.1f}, {rect.x1:.1f}, "
                                     f"{rect.y1:.1f}]")
                    for surname in result["skipped_outside"]:
                        self.log(f"  Стр. {i + 1}: '{surname}' найден, "
                                 f"но вне штампа — пропущено")
                except StampNotFoundError:
                    failed_pages.append(i + 1)
        finally:
            doc.close()

        if detected == 0:
            msg = ("Штамп не распознан ни на одной странице. "
                   "Включите «Ручной режим» или проверьте PDF.")
            logger.warning(msg)
            self._show_error(msg)
        elif failed_pages:
            msg = (f"Фамилии в штампе распознаны на {detected} стр. "
                   f"Не распознаны/пропущены страницы: {failed_pages}.")
            logger.warning(msg)
            self.log(msg)
        else:
            msg = f"Штамп успешно распознан на всех страницах ({detected} шт.)."
            logger.info(msg)
            self.log(msg)

    def choose_signer1_folder(self):
        path = filedialog.askdirectory(title="Выберите папку с подписями Подписанта 1")
        if path:
            self.signer1_folder.set(path)

    def choose_signer2_folder(self):
        path = filedialog.askdirectory(title="Выберите папку с подписями Подписанта 2")
        if path:
            self.signer2_folder.set(path)

    # ---------- Логирование ----------

    def log(self, message):
        """Добавляет сообщение в текстовое поле журнала."""
        self.log_text.configure(state="normal")
        self.log_text.insert("end", message + "\n")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")
        self.root.update_idletasks()

    def _show_error(self, message):
        """Показывает ошибку и в диалоге, и в журнале."""
        self.log(f"ОШИБКА: {message}")
        messagebox.showerror("Ошибка", message)

    # ---------- Запуск обработки ----------

    def on_process_clicked(self):
        pdf_path = self.pdf_path.get().strip()
        pages_str = self.pages_str.get().strip()
        folder1 = self.signer1_folder.get().strip()
        folder2 = self.signer2_folder.get().strip()

        # Сбрасываем placeholder, если пользователь его не трогал
        if pages_str == "1,10-16,21":
            pages_str = ""

        # 1. Проверка заполненности всех полей
        missing = []
        if not pdf_path:
            missing.append("PDF файл")
        if not folder1:
            missing.append("папка подписей Подписанта 1")
        if not folder2:
            missing.append("папка подписей Подписанта 2")
        if missing:
            self._show_error("Не заполнено: " + ", ".join(missing))
            return

        # 2. Проверка существования PDF-файла
        if not os.path.isfile(pdf_path):
            self._show_error(f"PDF файл не найден: {pdf_path}")
            return

        # 3. Парсинг списка страниц (пусто = все страницы документа)
        try:
            page_numbers = parse_pages(pages_str)
        except ValueError as e:
            self._show_error(str(e))
            return

        # 4. Проверка папок и наличия PNG-файлов
        try:
            signer1_pngs = find_png_files(folder1)
            signer2_pngs = find_png_files(folder2)
        except FileNotFoundError as e:
            self._show_error(str(e))
            return
        if not signer1_pngs:
            self._show_error(
                f"В папке Подписанта 1 нет PNG-файлов: {folder1}")
            return
        if not signer2_pngs:
            self._show_error(
                f"В папке Подписанта 2 нет PNG-файлов: {folder2}")
            return

        # 5. Обработка
        manual = bool(self.manual_mode.get())
        self.process_btn.configure(state="disabled")
        try:
            self.log("=" * 60)
            self.log(f"Старт. Файл: {pdf_path}")
            self.log(f"Режим: {'ручной (fallback)' if manual else 'автоопределение ячеек штампа'}")
            if page_numbers is None:
                self.log("Страницы: все (список не указан)")
            else:
                self.log(f"Страницы: {page_numbers}")
            self.log(f"Подписей Подписанта 1: {len(signer1_pngs)} шт., "
                     f"Подписанта 2: {len(signer2_pngs)} шт.")
            process_pdf(pdf_path, page_numbers,
                        signer1_pngs, signer2_pngs, self.log,
                        manual_mode=manual)
            self.log("Готово!")
            messagebox.showinfo("Готово!",
                                "Подписи вставлены, файл сохранён.")
        except Exception as e:
            self._show_error(str(e))
        finally:
            self.process_btn.configure(state="normal")


# ============================================================================
# ТОЧКА ВХОДА
# ============================================================================

def main():
    root = tk.Tk()
    SignatureApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
