#!/usr/bin/env python3
"""Render the fixed-instance P2 mathematical progress manuscript as a polished PDF.

The source manuscript is deliberately treated as read-only.  The renderer uses
ReportLab for the document, Matplotlib only for high-resolution display-math
images, and embeds the DejaVu font family in the resulting PDF.
"""

from __future__ import annotations

import argparse
import html
import re
import shutil
import sys
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from PIL import Image as PILImage
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY, TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    Image,
    Flowable,
    KeepTogether,
    PageBreak,
    Paragraph,
    Preformatted,
    SimpleDocTemplate,
    Spacer,
    Table,
    TableStyle,
)


TITLE = (
    "Artifact-Bound Non-Vacuous Single-Path Refinement "
    "of FreeRTOS V6.1.1 vTaskDelay(2)"
)
SHORT_TITLE = "FreeRTOS V6.1.1 Fixed P2 Witness"
STATUS_LINE = "Fixed P2 witness checked; universal functional correctness open"

NAVY = colors.HexColor("#17324D")
TEAL = colors.HexColor("#177D7A")
BLUE = colors.HexColor("#2E6F9E")
INK = colors.HexColor("#17212B")
MUTED = colors.HexColor("#52606D")
PALE_BLUE = colors.HexColor("#EEF5FA")
PALE_GREEN = colors.HexColor("#ECF7F4")
PALE_GRAY = colors.HexColor("#F3F5F7")
RULE = colors.HexColor("#B9C6D2")


def normalize_text(value: str) -> str:
    """Normalize troublesome punctuation while retaining mathematical glyphs."""
    return (
        value.replace("\u2010", "-")
        .replace("\u2011", "-")
        .replace("\u2012", "-")
        .replace("\u2013", "-")
        .replace("\u2014", "-")
        .replace("\u2212", "-")
        .replace("\u00a0", " ")
    )


def find_font_dir(explicit: Path | None) -> Path:
    candidates = [
        explicit,
        Path("C:/Windows/Fonts"),
        Path(
            "C:/Users/Chengsong/.cache/codex-runtimes/codex-primary-runtime/"
            "dependencies/native/poppler/Library/share/fonts"
        ),
        Path("/usr/share/fonts/truetype/dejavu"),
    ]
    required = [
        "DejaVuSans.ttf",
        "DejaVuSans-Bold.ttf",
        "DejaVuSans-Oblique.ttf",
        "DejaVuSans-BoldOblique.ttf",
        "DejaVuSansMono.ttf",
    ]
    for candidate in candidates:
        if candidate and all((candidate / name).is_file() for name in required):
            return candidate
    raise FileNotFoundError("Could not locate the complete DejaVu font family")


def register_fonts(font_dir: Path) -> None:
    font_files = {
        "DejaVuSans": "DejaVuSans.ttf",
        "DejaVuSans-Bold": "DejaVuSans-Bold.ttf",
        "DejaVuSans-Oblique": "DejaVuSans-Oblique.ttf",
        "DejaVuSans-BoldOblique": "DejaVuSans-BoldOblique.ttf",
        "DejaVuSansMono": "DejaVuSansMono.ttf",
    }
    for family, filename in font_files.items():
        pdfmetrics.registerFont(TTFont(family, str(font_dir / filename)))
    pdfmetrics.registerFontFamily(
        "DejaVuSans",
        normal="DejaVuSans",
        bold="DejaVuSans-Bold",
        italic="DejaVuSans-Oblique",
        boldItalic="DejaVuSans-BoldOblique",
    )


def tex_to_plain(value: str) -> str:
    """Convert short inline TeX fragments to legible Unicode text."""
    value = normalize_text(value)
    # Strip sizing commands before replacing symbols: otherwise the prefix
    # ``\le`` in ``\left`` would become the less-than-or-equal glyph.
    for structural in (r"\left", r"\right", r"\bigl", r"\bigr", r"\Bigl", r"\Bigr"):
        value = value.replace(structural, "")
    replacements = {
        r"\Longleftrightarrow": "\u21d4",
        r"\Longrightarrow": "\u21d2",
        r"\longrightarrow": "\u27f6",
        r"\Rightarrow": "\u21d2",
        r"\rightarrow": "\u2192",
        r"\curvearrowright": "\u21dd",
        r"\mapsto": "\u21a6",
        r"\equiv": "\u2261",
        r"\nless": "\u226e",
        r"\not<": "\u226e",
        r"\notin": "\u2209",
        r"\emptyset": "\u2205",
        r"\varnothing": "\u2205",
        r"\wedge": "\u2227",
        r"\land": "\u2227",
        r"\vee": "\u2228",
        r"\lor": "\u2228",
        r"\forall": "\u2200",
        r"\exists": "\u2203",
        r"\in": "\u2208",
        r"\ne": "\u2260",
        r"\le": "\u2264",
        r"\ge": "\u2265",
        r"\neg": "\u00ac",
        r"\cap": "\u2229",
        r"\subseteq": "\u2286",
        r"\gets": "\u2190",
        r"\cdot": "\u00b7",
        r"\bullet": "\u2022",
        r"\epsilon": "\u03b5",
        r"\lambda": "\u03bb",
        r"\phi": "\u03c6",
        r"\pi": "\u03c0",
        r"\ell": "\u2113",
        r"\not<": "\u226e",
        r"\le": "\u2264",
        r"\ge": "\u2265",
        r"\to": "\u2192",
        r"\qquad": "  ",
        r"\quad": " ",
        r"\;": " ",
        r"\,": " ",
        r"\!": "",
    }
    # Longest-first avoids prefix collisions such as \ne / \neg and \ge / \gets.
    for source in sorted(replacements, key=len, reverse=True):
        target = replacements[source]
        value = value.replace(source, target)
    command = re.compile(
        r"\\(?:operatorname|mathrm|mathsf|mathcal|mathbf|text)\{([^{}]*)\}"
    )
    previous = None
    while previous != value:
        previous = value
        value = command.sub(r"\1", value)
    value = re.sub(
        r"\\(?:operatorname|mathrm|mathsf|mathcal|mathbf|text)\s+([A-Za-z])",
        r"\1",
        value,
    )
    value = re.sub(r"\\(?:mathcal|mathbf|mathsf)\s*([A-Za-z])", r"\1", value)
    value = value.replace(r"\_", "_")
    value = re.sub(r"_\{([^{}]+)\}", r"_(\1)", value)
    value = re.sub(r"\^\{([^{}]+)\}", r"^(\1)", value)
    value = value.replace(r"\left", "").replace(r"\right", "")
    value = value.replace(r"\bigl", "").replace(r"\bigr", "")
    value = value.replace("{", "").replace("}", "")
    value = re.sub(r"\\([A-Za-z]+)", r"\1", value)
    return re.sub(r"\s+", " ", value).strip()


def format_inline(value: str) -> str:
    """Translate the small Markdown subset used by the manuscript."""
    value = normalize_text(value.strip())
    value = html.escape(value, quote=False)
    value = value.replace("[^draft]", "<super>1</super>")
    value = re.sub(
        r"`([^`]+)`",
        r'<font name="DejaVuSansMono" color="#214A64">\1</font>',
        value,
    )

    def math_sub(match: re.Match[str]) -> str:
        plain = html.escape(tex_to_plain(html.unescape(match.group(1))), quote=False)
        return f'<font name="DejaVuSans-Oblique" color="#163F59">{plain}</font>'

    value = re.sub(r"\$([^$]+)\$", math_sub, value)
    value = re.sub(r"\*\*([^*]+)\*\*", r"<b>\1</b>", value)
    value = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<i>\1</i>", value)
    return value


def make_styles(body_size: float) -> dict[str, ParagraphStyle]:
    base = getSampleStyleSheet()
    return {
        "Title": ParagraphStyle(
            "Title",
            parent=base["Title"],
            fontName="DejaVuSans-Bold",
            fontSize=17.5,
            leading=20.5,
            textColor=NAVY,
            alignment=TA_CENTER,
            spaceAfter=7,
        ),
        "Meta": ParagraphStyle(
            "Meta",
            parent=base["Normal"],
            fontName="DejaVuSans",
            fontSize=8.1,
            leading=10.2,
            textColor=MUTED,
            alignment=TA_CENTER,
            spaceAfter=2,
        ),
        "Heading1": ParagraphStyle(
            "Heading1",
            parent=base["Heading1"],
            fontName="DejaVuSans-Bold",
            fontSize=12.2,
            leading=14.4,
            textColor=NAVY,
            spaceBefore=7,
            spaceAfter=4,
            keepWithNext=True,
        ),
        "Heading2": ParagraphStyle(
            "Heading2",
            parent=base["Heading2"],
            fontName="DejaVuSans-Bold",
            fontSize=9.8,
            leading=12,
            textColor=TEAL,
            spaceBefore=5,
            spaceAfter=3,
            keepWithNext=True,
        ),
        "Body": ParagraphStyle(
            "Body",
            parent=base["BodyText"],
            fontName="DejaVuSans",
            fontSize=body_size,
            leading=body_size * 1.27,
            textColor=INK,
            alignment=TA_LEFT,
            spaceAfter=3.2,
            allowWidows=0,
            allowOrphans=0,
        ),
        "BodyLeft": ParagraphStyle(
            "BodyLeft",
            parent=base["BodyText"],
            fontName="DejaVuSans",
            fontSize=body_size,
            leading=body_size * 1.27,
            textColor=INK,
            alignment=TA_LEFT,
            spaceAfter=2.5,
        ),
        "Bullet": ParagraphStyle(
            "Bullet",
            parent=base["BodyText"],
            fontName="DejaVuSans",
            fontSize=body_size,
            leading=body_size * 1.25,
            textColor=INK,
            leftIndent=12,
            firstLineIndent=0,
            bulletIndent=1,
            spaceAfter=1.8,
        ),
        "Code": ParagraphStyle(
            "Code",
            parent=base["Code"],
            fontName="DejaVuSansMono",
            fontSize=6.9,
            leading=8.4,
            leftIndent=7,
            rightIndent=7,
            spaceBefore=2,
            spaceAfter=4,
            textColor=colors.HexColor("#20313F"),
            backColor=None,
            borderColor=None,
            borderWidth=0,
            borderPadding=0,
        ),
        "TableHeader": ParagraphStyle(
            "TableHeader",
            parent=base["Normal"],
            fontName="DejaVuSans-Bold",
            fontSize=6.7,
            leading=8,
            textColor=colors.white,
            alignment=TA_LEFT,
        ),
        "TableCell": ParagraphStyle(
            "TableCell",
            parent=base["Normal"],
            fontName="DejaVuSans",
            fontSize=6.35,
            leading=7.8,
            textColor=INK,
            alignment=TA_LEFT,
            splitLongWords=True,
        ),
        "Quote": ParagraphStyle(
            "Quote",
            parent=base["BodyText"],
            fontName="DejaVuSans",
            fontSize=body_size - 0.15,
            leading=(body_size - 0.15) * 1.27,
            textColor=INK,
            alignment=TA_LEFT,
            spaceAfter=2,
        ),
        "Footnote": ParagraphStyle(
            "Footnote",
            parent=base["BodyText"],
            fontName="DejaVuSans",
            fontSize=6.4,
            leading=8,
            textColor=MUTED,
            leftIndent=8,
            firstLineIndent=-8,
            spaceBefore=4,
        ),
    }


def _math_lines(tex: str) -> list[str]:
    value = normalize_text(tex.strip())
    boxed = "\\boxed{" in value
    value = value.replace(r"\boxed{", "")
    value = value.replace(r"\begin{aligned}", "")
    value = value.replace(r"\end{aligned}", "")
    if boxed and value.rstrip().endswith("}"):
        value = value.rstrip()[:-1]
    value = re.sub(r"\\\\(?:\[[^]]*\])?", "\n", value)
    lines: list[str] = []
    for line in value.splitlines():
        line = line.strip().lstrip(">").strip().replace("&", "")
        line = line.replace(r"\operatorname", r"\mathrm")
        line = line.replace(r"\text", r"\mathrm")
        line = line.replace(r"\land", r"\wedge")
        line = line.replace(r"\lor", r"\vee")
        line = line.replace(r"\not<", r"\nless")
        line = line.replace(r"\not>", r"\ngtr")
        line = re.sub(
            r"\\(mathcal|mathbf|mathsf)\s+([A-Za-z])",
            r"\\\1{\2}",
            line,
        )
        line = line.replace(r"\left", "").replace(r"\right", "")
        line = line.replace(r"\bigl", "").replace(r"\bigr", "")
        line = line.replace(r"\Bigl", "").replace(r"\Bigr", "")
        line = line.replace("{}", "")
        if line:
            lines.append(line)
    return lines or [tex_to_plain(tex)]


def render_math_line(
    tex: str,
    path: Path,
    max_width: float,
    max_height: float = 25.0,
) -> Image | Preformatted:
    """Render one display-math line, falling back to readable plain text."""
    try:
        plt.rcParams.update(
            {
                "mathtext.fontset": "dejavusans",
                "font.family": "DejaVu Sans",
                "font.size": 10,
            }
        )
        figure = plt.figure(figsize=(10, 0.45), dpi=240)
        figure.patch.set_alpha(0)
        figure.text(0.01, 0.50, f"${tex}$", ha="left", va="center", color="#163F59")
        figure.savefig(path, dpi=240, bbox_inches="tight", pad_inches=0.035, transparent=True)
        plt.close(figure)
        with PILImage.open(path) as image:
            px_width, px_height = image.size
        natural_width = px_width * 72 / 240
        natural_height = px_height * 72 / 240
        scale = min(1.0, max_width / natural_width, max_height / natural_height)
        return Image(
            str(path),
            width=max(1.0, natural_width * scale),
            height=max(1.0, natural_height * scale),
        )
    except Exception:
        plt.close("all")
        fallback = ParagraphStyle(
            "EquationFallback",
            fontName="DejaVuSansMono",
            fontSize=6.8,
            leading=8.4,
            textColor=BLUE,
        )
        return Preformatted(tex_to_plain(tex), fallback)


class EquationBlock(Flowable):
    """Atomic vector-text equation group laid out inside the normal frame."""

    def __init__(self, paragraphs: Sequence[Paragraph]) -> None:
        super().__init__()
        self.paragraphs = list(paragraphs)
        self._layout: list[tuple[Paragraph, float, float]] = []

    def wrap(self, avail_width: float, avail_height: float) -> tuple[float, float]:
        self._layout = []
        total_height = 0.0
        for paragraph in self.paragraphs:
            width, height = paragraph.wrap(avail_width, 100000)
            self._layout.append((paragraph, width, height))
            total_height += height
        self.width = avail_width
        self.height = total_height
        return avail_width, total_height

    def draw(self) -> None:
        y = self.height
        for paragraph, _width, height in self._layout:
            y -= height
            paragraph.drawOn(self.canv, 0, y)


class Renderer:
    def __init__(
        self,
        styles: dict[str, ParagraphStyle],
        tmp_dir: Path,
        content_width: float,
    ) -> None:
        self.styles = styles
        self.tmp_dir = tmp_dir
        self.content_width = content_width
        self.equation_number = 0

    def equation(self, tex: str, in_box: bool = False):
        lines = _math_lines(tex)
        equation_style = ParagraphStyle(
            "Equation",
            parent=self.styles["BodyLeft"],
            fontName="DejaVuSans-Oblique",
            fontSize=8.55,
            leading=10.6,
            textColor=colors.HexColor("#163F59"),
            alignment=TA_CENTER if len(lines) == 1 else TA_LEFT,
            leftIndent=6 if len(lines) > 1 else 0,
            rightIndent=4,
            spaceAfter=0,
        )
        paragraphs = [
            Paragraph(html.escape(tex_to_plain(line)), equation_style) for line in lines
        ]
        if in_box:
            nested = Table([[paragraphs]], colWidths=[self.content_width - 34])
            nested.setStyle(
                TableStyle(
                    [
                        ("VALIGN", (0, 0), (-1, -1), "TOP"),
                        ("LEFTPADDING", (0, 0), (-1, -1), 0),
                        ("RIGHTPADDING", (0, 0), (-1, -1), 0),
                        ("TOPPADDING", (0, 0), (-1, -1), 0),
                        ("BOTTOMPADDING", (0, 0), (-1, -1), 0),
                    ]
                )
            )
            return nested
        return EquationBlock(paragraphs)

    def markdown_table(self, rows: Sequence[Sequence[str]]) -> Table:
        ncols = max(len(row) for row in rows)
        padded = [list(row) + [""] * (ncols - len(row)) for row in rows]
        header = []
        for cell in padded[0]:
            formatted = re.sub(r' color="#[0-9A-Fa-f]{6}"', "", format_inline(cell))
            header.append(Paragraph(formatted, self.styles["TableHeader"]))
        body = [
            [Paragraph(format_inline(cell), self.styles["TableCell"]) for cell in row]
            for row in padded[1:]
        ]
        heading = " ".join(padded[0]).lower()
        if ncols == 2:
            fractions = [0.24, 0.76]
        elif ncols == 3 and "component" in heading:
            fractions = [0.27, 0.365, 0.365]
        elif ncols == 3:
            fractions = [0.24, 0.51, 0.25]
        elif ncols == 4 and "run identifier" in heading:
            # Run identifiers are long and must wrap in a deliberately wide
            # evidence column; equal quarters create tall, brittle rows.
            fractions = [0.20, 0.48, 0.12, 0.20]
        elif ncols == 5:
            fractions = [0.22, 0.235, 0.105, 0.13, 0.31]
        else:
            fractions = [1 / ncols] * ncols
        widths = [self.content_width * fraction for fraction in fractions]
        table = Table([header] + body, colWidths=widths, repeatRows=1, splitByRow=1)
        table.setStyle(
            TableStyle(
                [
                    ("BACKGROUND", (0, 0), (-1, 0), NAVY),
                    ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
                    ("VALIGN", (0, 0), (-1, -1), "TOP"),
                    ("GRID", (0, 0), (-1, -1), 0.35, RULE),
                    ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, PALE_GRAY]),
                    ("LEFTPADDING", (0, 0), (-1, -1), 3.2),
                    ("RIGHTPADDING", (0, 0), (-1, -1), 3.2),
                    ("TOPPADDING", (0, 0), (-1, -1), 2.5),
                    ("BOTTOMPADDING", (0, 0), (-1, -1), 2.5),
                ]
            )
        )
        return table

    @staticmethod
    def _is_special(lines: Sequence[str], index: int) -> bool:
        line = lines[index].strip()
        if not line:
            return True
        if line == "<!-- pagebreak -->":
            return True
        if line.startswith(("#", "```", ">", "[^draft]:")):
            return True
        if line == "$$":
            return True
        if line.startswith("|"):
            return True
        if re.match(r"^(?:[-*]|\d+\.)\s+", line):
            return True
        return False

    def parse(self, lines: Sequence[str], *, nested: bool = False) -> list:
        flowables: list = []
        index = 0
        while index < len(lines):
            raw = lines[index].rstrip()
            stripped = raw.strip()
            if not stripped:
                index += 1
                continue

            if stripped == "<!-- pagebreak -->":
                # A tiny ordinary flowable after the break anchors the next
                # frame before a custom equation block or keep-with-next
                # heading is laid out.
                flowables.extend([PageBreak(), Spacer(1, 0.1)])
                index += 1
                continue

            if stripped.startswith("[^draft]:"):
                note = stripped.split(":", 1)[1].strip()
                flowables.append(
                    Paragraph(f"<b>1.</b> {format_inline(note)}", self.styles["Footnote"])
                )
                index += 1
                continue

            if stripped.startswith(">"):
                quote_lines: list[str] = []
                while index < len(lines) and lines[index].lstrip().startswith(">"):
                    quote_lines.append(re.sub(r"^\s*>\s?", "", lines[index].rstrip()))
                    index += 1
                inner = self.parse(quote_lines, nested=True)
                theorem = any("Theorem Box" in line for line in quote_lines)
                box = Table([[inner]], colWidths=[self.content_width - (18 if nested else 0)])
                box.setStyle(
                    TableStyle(
                        [
                            (
                                "BACKGROUND",
                                (0, 0),
                                (-1, -1),
                                PALE_GREEN if theorem else PALE_BLUE,
                            ),
                            ("BOX", (0, 0), (-1, -1), 0.8, TEAL if theorem else BLUE),
                            ("LINEBEFORE", (0, 0), (0, -1), 3, TEAL if theorem else BLUE),
                            ("LEFTPADDING", (0, 0), (-1, -1), 8),
                            ("RIGHTPADDING", (0, 0), (-1, -1), 8),
                            ("TOPPADDING", (0, 0), (-1, -1), 6),
                            ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
                        ]
                    )
                )
                flowables.extend([box, Spacer(1, 4)])
                continue

            if stripped == "$$":
                math_lines: list[str] = []
                index += 1
                while index < len(lines) and lines[index].strip() != "$$":
                    math_lines.append(lines[index])
                    index += 1
                index += 1
                equation = self.equation("\n".join(math_lines), nested)
                if isinstance(equation, list):
                    flowables.extend(equation)
                else:
                    flowables.append(equation)
                flowables.append(Spacer(1, 3))
                continue

            if stripped.startswith("```"):
                code_lines: list[str] = []
                index += 1
                while index < len(lines) and not lines[index].strip().startswith("```"):
                    code_lines.append(normalize_text(lines[index].rstrip()))
                    index += 1
                index += 1
                # A split Preformatted fragment can inherit a page-level clipping
                # path in ReportLab and obscure running matter on the continuation
                # page.  The report's diagrams all fit in one frame, so keep each
                # one atomic and move it to the next page when necessary.
                flowables.append(
                    KeepTogether(
                        [Preformatted("\n".join(code_lines), self.styles["Code"])]
                    )
                )
                continue

            if stripped.startswith("|") and index + 1 < len(lines):
                table_lines: list[str] = []
                while index < len(lines) and lines[index].strip().startswith("|"):
                    table_lines.append(lines[index].strip())
                    index += 1

                def cells(line: str) -> list[str]:
                    return [part.strip() for part in line.strip().strip("|").split("|")]

                parsed = [cells(line) for line in table_lines]
                if len(parsed) >= 2 and all(
                    re.fullmatch(r":?-{3,}:?", cell) for cell in parsed[1]
                ):
                    parsed.pop(1)
                flowables.extend([self.markdown_table(parsed), Spacer(1, 4)])
                continue

            heading = re.match(r"^(#{1,3})\s+(.+)$", stripped)
            if heading:
                level = len(heading.group(1))
                content = format_inline(heading.group(2))
                if level == 1 and not nested:
                    flowables.extend(
                        [Spacer(1, 2 * mm), Paragraph(content, self.styles["Title"])]
                    )
                else:
                    style = self.styles["Heading1" if level == 2 else "Heading2"]
                    flowables.append(Paragraph(content, style))
                index += 1
                continue

            list_match = re.match(r"^([-*]|\d+\.)\s+(.+)$", stripped)
            if list_match:
                marker, content = list_match.groups()
                bullet = "\u2022" if marker in {"-", "*"} else marker
                flowables.append(
                    Paragraph(
                        format_inline(content), self.styles["Bullet"], bulletText=bullet
                    )
                )
                index += 1
                continue

            paragraph_lines = [stripped]
            index += 1
            while index < len(lines) and not self._is_special(lines, index):
                paragraph_lines.append(lines[index].strip())
                index += 1
            paragraph = " ".join(part for part in paragraph_lines if part)
            if len(paragraph_lines) > 1 and all(
                part.startswith("**") and part.rstrip().endswith("**")
                for part in paragraph_lines
            ):
                for part in paragraph_lines:
                    flowables.append(Paragraph(format_inline(part), self.styles["Meta"]))
                continue
            if paragraph.startswith("**") and paragraph.endswith("**"):
                style = self.styles["Meta"] if not nested else self.styles["Quote"]
            else:
                style = self.styles["Quote"] if nested else self.styles["Body"]
            flowables.append(Paragraph(format_inline(paragraph), style))
        return flowables


class ProgressDocTemplate(SimpleDocTemplate):
    def afterFlowable(self, flowable) -> None:  # noqa: N802 - ReportLab callback
        if not isinstance(flowable, Paragraph):
            return
        style_name = flowable.style.name
        if style_name not in {"Heading1", "Heading2"}:
            return
        level = 0 if style_name == "Heading1" else 1
        key = f"outline-{self.page}-{id(flowable)}"
        title = re.sub(r"<[^>]+>", "", flowable.getPlainText())
        self.canv.bookmarkPage(key)
        self.canv.addOutlineEntry(title, key, level=level, closed=False)

def header_footer(canvas, document) -> None:
    canvas.saveState()
    width, height = A4
    left = document.leftMargin
    right = width - document.rightMargin
    if document.page > 1:
        canvas.setStrokeColor(RULE)
        canvas.setLineWidth(0.45)
        canvas.line(left, height - 12.2 * mm, right, height - 12.2 * mm)
        canvas.setFont("DejaVuSans", 6.8)
        canvas.setFillColor(MUTED)
        canvas.drawString(left, height - 9.6 * mm, SHORT_TITLE)
        canvas.drawRightString(right, height - 9.6 * mm, "Status date: 2 August 2026")
    canvas.setStrokeColor(RULE)
    canvas.setLineWidth(0.45)
    canvas.line(left, 11.5 * mm, right, 11.5 * mm)
    canvas.setFont("DejaVuSans", 6.3)
    canvas.setFillColor(MUTED)
    canvas.drawString(left, 8.2 * mm, STATUS_LINE)
    canvas.drawRightString(right, 8.2 * mm, f"Page {document.page}")
    canvas.restoreState()


def render(input_path: Path, output_path: Path, tmp_dir: Path, font_dir: Path, body_size: float) -> None:
    if not input_path.is_file():
        raise FileNotFoundError(f"Manuscript not found: {input_path}")
    register_fonts(font_dir)
    tmp_dir.mkdir(parents=True, exist_ok=True)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    for old in tmp_dir.glob("equation-*.png"):
        old.unlink()

    margins = dict(leftMargin=15 * mm, rightMargin=15 * mm, topMargin=17 * mm, bottomMargin=16 * mm)
    document = ProgressDocTemplate(
        str(output_path),
        pagesize=A4,
        title=TITLE,
        author="Blind Isabelle/HOL reconstruction project",
        subject="Fixed-instance FreeRTOS V6.1.1 P2 source-to-abstract witness; universal correctness open",
        creator="ReportLab renderer with embedded DejaVu fonts",
        **margins,
    )
    content_width = A4[0] - margins["leftMargin"] - margins["rightMargin"]
    styles = make_styles(body_size)
    renderer = Renderer(styles, tmp_dir, content_width)
    manuscript = normalize_text(input_path.read_text(encoding="utf-8"))
    story = renderer.parse(manuscript.splitlines())
    document.build(
        story,
        onFirstPage=header_footer,
        onLaterPages=header_footer,
    )


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    script = Path(__file__).resolve()
    repo = script.parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input",
        type=Path,
        default=repo / "docs" / "FREERTOS_V611_P2_MATHEMATICAL_PROGRESS.md",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=repo / "output" / "pdf" / "freertos_v611_p2_mathematical_progress.pdf",
    )
    parser.add_argument("--tmp", type=Path, default=repo / "tmp" / "pdfs")
    parser.add_argument("--font-dir", type=Path)
    parser.add_argument("--body-size", type=float, default=8.15)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    font_dir = find_font_dir(args.font_dir)
    render(args.input.resolve(), args.output.resolve(), args.tmp.resolve(), font_dir, args.body_size)
    print(args.output.resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
