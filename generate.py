import html
import os
from pathlib import Path
from typing import Iterable
import re


ROOT = Path(__file__).parent
BLOG_DIR = ROOT / "blog"
TITLE = "Logic Sea"


def timestamp() -> str:
    return os.popen("date").read().strip()


def canonical_blog_posts() -> list[Path]:
    posts = []
    for path in BLOG_DIR.glob("*.html"):
        name = path.name
        if name in {"blog.html", "main.html"}:
            continue
        if ".html.html" in name:
            continue
        posts.append(path)
    return sorted(posts, key=lambda p: p.stat().st_mtime, reverse=True)


def post_title(path: Path) -> str:
    stem = path.stem.replace("_", " ").strip()
    return stem.title()


def extract_legacy_content(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    match = re.search(r'<div id="content">(.*)</div>\s*<div id=update_bar>', text, re.S)
    if match:
        return match.group(1).strip()
    return text


def nav(current: str, prefix: str = "") -> str:
    items = [
        ("home", "Home", f"{prefix}index.html"),
        ("about", "About", f"{prefix}about/about.html"),
        ("research", "Research", f"{prefix}research/research.html"),
        ("courses", "Course Notes", f"{prefix}courses/courses.html"),
        ("blog", "Blog", f"{prefix}blog/blog.html"),
    ]

    rendered = []
    for key, label, href in items:
        cls = ' class="current"' if key == current else ""
        rendered.append(f'<a{cls} href="{href}">{label}</a>')
    return '<nav class="site-nav">' + "".join(rendered) + "</nav>"


def layout(title: str, current: str, body: str, prefix: str = "") -> str:
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="description" content="Logic, geometry, formal methods, and computation.">
  <title>{html.escape(title)} | {TITLE}</title>
  <link rel="stylesheet" type="text/css" href="{prefix}greywhite.css">
</head>
<body>
  <div class="page-shell">
    <header class="site-header">
      <a class="site-brand" href="{prefix}index.html">{TITLE}</a>
      {nav(current, prefix)}
    </header>
    <main id="content">
      {body}
    </main>
    <footer id="update_bar">
      <p>Compiled: {html.escape(timestamp())}</p>
    </footer>
  </div>
</body>
</html>
"""


def write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def section(title: str, content: str) -> str:
    return f"""
    <section class="panel">
      <h2>{html.escape(title)}</h2>
      {content}
    </section>
    """


def cards(items: Iterable[tuple[str, str, str]]) -> str:
    inner = []
    for title, text, href in items:
        inner.append(
            f"""
            <article class="card">
              <h3>{html.escape(title)}</h3>
              <p>{text}</p>
              <p><a href="{href}">Read more</a></p>
            </article>
            """
        )
    return '<section class="card-grid">' + "".join(inner) + "</section>"


def build_home() -> None:
    body = f"""
    <section class="hero">
      <p class="eyebrow">Mathematics and Computation</p>
      <h1>Logic, geometry, formal methods, and structured curiosity.</h1>
      <p class="lead">
        This site collects research interests, notes, course material, and
        essays on mathematics, programming languages, formal reasoning, and
        related projects.
      </p>
      <div class="hero-links">
        <a href="research/research.html">Research overview</a>
        <a href="courses/courses.html">Course notes</a>
        <a href="blog/blog.html">Recent writing</a>
      </div>
    </section>

    {cards([
        ("About", "A short overview of what this site is for and how the material is organized.", "about/about.html"),
        ("Research", "Current themes in logic, geometry, constructive mathematics, and formal systems.", "research/research.html"),
        ("Course Notes", "Archived notes from courses in logic, algebra, compilers, and related topics.", "courses/courses.html"),
    ])}

    {section("What You Will Find", """
      <ul class="clean-list">
        <li>Research directions and long-form project ideas</li>
        <li>Course notes and reading trails</li>
        <li>Essays and short blog posts</li>
        <li>Links out to software and formalization projects</li>
      </ul>
    """)}
    """
    write(ROOT / "index.html", layout("Home", "home", body))


def build_about() -> None:
    body = f"""
    <section class="hero small-hero">
      <p class="eyebrow">About</p>
      <h1>A personal research notebook without the noise.</h1>
      <p class="lead">
        This website is meant to be a simple home for mathematical interests,
        technical writing, course notes, and software-adjacent research ideas.
      </p>
    </section>

    {cards([
        ("Logic", "Interests in proof, semantics, automated reasoning, and the structure of formal systems.", "../research/research.html"),
        ("Geometry", "A recurring pull toward topology, algebraic geometry, representation theory, and geometric structure.", "../research/research.html"),
        ("Computation", "Programming languages, compilers, formalization tools, and mathematical software projects.", "../courses/courses.html"),
    ])}

    {section("Why This Site Exists", """
      <p>
        The older version of the site accumulated useful material, but it did
        not explain itself very well. This version is meant to make the content
        easier to navigate and easier to maintain.
      </p>
      <p>
        It is intentionally lightweight: plain HTML, a small stylesheet, and a
        simple Python generator for the top-level pages.
      </p>
    """)}
    """
    write(ROOT / "about" / "about.html", layout("About", "about", body, "../"))


def build_research() -> None:
    body = f"""
    <section class="hero small-hero">
      <p class="eyebrow">Research</p>
      <h1>Foundations, structure, and formal mathematical tools.</h1>
      <p class="lead">
        Current interests sit near the intersection of logic, geometry,
        algebra, programming languages, and constructive mathematics.
      </p>
    </section>

    {section("Current Themes", """
      <ul class="clean-list">
        <li>Logic and automated reasoning</li>
        <li>Program synthesis and verification</li>
        <li>Constructive mathematics and formalization</li>
        <li>Algebra, representation theory, and geometry</li>
        <li>Mathematical structures underlying computation</li>
      </ul>
    """)}

    {section("Selected Work", """
      <ul class="clean-list">
        <li><a href="https://github.com/PurdueDualityLab/deepbugs-jr" target="_blank" rel="noreferrer">Reproduction of "DeepBugs: A Learning Approach to Name-based Bug Detection"</a></li>
        <li><a href="https://github.com/Jmw150/Brain-Generator" target="_blank" rel="noreferrer">BrainGan: A brain-oriented image generation project</a></li>
        <li><a href="https://github.com/Jmw150" target="_blank" rel="noreferrer">Additional software and formalization projects on GitHub</a></li>
      </ul>
    """)}

    {section("Reading Trail", """
      <p>Some books and traditions that continue to shape the material here:</p>
      <ul class="clean-list">
        <li>Abstract Algebra by Dummit and Foote</li>
        <li>Commutative Algebra by Eisenbud</li>
        <li>Algebraic Geometry by Hartshorne</li>
        <li>Introduction to Mathematical Logic by Mendelson</li>
        <li>Model Theory by Marker</li>
      </ul>
    """)}
    """
    write(ROOT / "research" / "research.html", layout("Research", "research", body, "../"))


def build_courses() -> None:
    body = f"""
    <section class="hero small-hero">
      <p class="eyebrow">Course Notes</p>
      <h1>Archived notes and reading from mathematics and computing courses.</h1>
      <p class="lead">
        These pages collect notes, pointers, and short reflections connected to
        coursework and independent reading.
      </p>
    </section>

    {section("Fall 2022", """
      <ul class="clean-list">
        <li><a href="abstract_algebra/abstract_algebra.html">MA 553 Abstract Algebra</a></li>
        <li><a href="commutative_algebra/commutative_algebra.html">MA 557 Commutative Algebra</a></li>
        <li><a href="compilers/compilers.html">ECE 573 Compilers and Translator Writing Systems</a></li>
        <li><a href="algorithms/algorithms.html">ECE 608 Computational Models and Methods</a></li>
        <li><a href="research_fall_2022/research_fall_2022.html">ECE 699 PhD Research</a></li>
      </ul>
    """)}

    {section("2021-2022", """
      <ul class="clean-list">
        <li><a href="summer_of_algebra/summer_of_algebra.html">Summer of Algebra</a></li>
        <li><a href="ece_seminar_class/ece_seminar_class.html">ECE 694 Seminar Course</a></li>
        <li><a href="research_spring_2022/research_spring_2022.html">ECE 699 PhD Research</a></li>
        <li><a href="dl/dl.html">ECE 595 Deep Learning</a></li>
        <li><a href="research_fall_2021/research_fall_2021.html">ECE 696 Active Program Synthesis</a></li>
      </ul>
    """)}

    {section("2020-2021", """
      <ul class="clean-list">
        <li><a href="summer_of_logic/summer_of_logic.html">Summer of Logic</a></li>
        <li><a href="adv_compilers/adv_compilers.html">ECE 663 Advanced Compilers</a></li>
        <li><a href="software_engineering/software_engineering.html">ECE 595 Advanced Software Engineering</a></li>
        <li><a href="set_theory/set_theory.html">MA 598 Set Theory</a></li>
        <li><a href="mathemetical_logic/mathemetical_logic.html">MA 585 Mathematical Logic</a></li>
        <li><a href="intro_compilers/intro_compilers.html">ECE 595 Intro to Compilers</a></li>
      </ul>
    """)}
    """
    write(ROOT / "courses" / "courses.html", layout("Course Notes", "courses", body, "../"))


def build_blog() -> None:
    cards_html = []
    for post in canonical_blog_posts():
        mtime = post.stat().st_mtime
        updated = os.popen(f"date -d '@{int(mtime)}' '+%Y-%m-%d'").read().strip()
        cards_html.append(
            f"""
            <article class="card">
              <h3>{html.escape(post_title(post))}</h3>
              <p class="meta">Updated: {html.escape(updated)}</p>
              <p><a href="{post.name}">Open post</a></p>
            </article>
            """
        )

        post_body = f"""
        <section class="hero small-hero">
          <p class="eyebrow">Blog Post</p>
          <h1>{html.escape(post_title(post))}</h1>
          <p class="lead">Archived note or essay from the blog.</p>
        </section>

        <section class="panel prose">
          {extract_legacy_content(post)}
        </section>
        """
        write(post, layout(post_title(post), "blog", post_body, "../"))

    body = f"""
    <section class="hero small-hero">
      <p class="eyebrow">Blog</p>
      <h1>Short essays, questions, and mathematical detours.</h1>
      <p class="lead">
        A collection of posts that are more exploratory or reflective than the
        main research pages.
      </p>
    </section>

    <section class="card-grid">
      {''.join(cards_html)}
    </section>
    """
    write(BLOG_DIR / "blog.html", layout("Blog", "blog", body, "../"))


def main() -> None:
    build_home()
    build_about()
    build_research()
    build_courses()
    build_blog()


if __name__ == "__main__":
    main()
