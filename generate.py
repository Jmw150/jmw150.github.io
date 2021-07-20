# A python script to generate websites
# Jordan Winkler


import time 
import os

# Paths
# {{{
css = 'bluestyle.css'
data = 'data'
home_path = 'index.html'
research_path = 'research/research.html'
course_path = 'courses/courses.html'
blog_path = 'blog/blog.html'
blogs_source = '../../blog/'
# }}}

lname = link_name = lambda name, link : '<a href='+link+'>'+name+'</a>'
listlink = lambda name, link : '<br><a href='+link+'>'+name+'</a>'

## all websites are a minimal of {name, data} 
class Page :
    "A website page"
    def __init__(self, name, data=' ', next=None, prev=None, up=None):
        self.name = name
        self.data = data

        # extra possible metadata
        self.next = next
        self.prev = prev
        self.up   = up


def get_file(filename) :
    File = ""
    with open(filename) as f:
        for l in f.readlines() :
            File += l

    return File

def get_blogs(path) :
    bloglist = os.popen('ls -t '+path).read().split('\n')[:-1]
    blogs = []
    # add title to work, and clump together
    for i in bloglist :
        file = ('\n  <h2>'+i.replace('_',' ')+'</h2>\n'
                +get_file(path+'/'+i)) # add dates later?
        blogs.append(Page(i,file))
    
    return blogs

# website data
# {{{

# nav_bar
# {{{
nav_bar = lambda css, home, research, courses, blog : """
<!DOCTYPE html PUBLIC "-//w3c//dtd html 5.0 transitional//en">
<html>
 <head>
   <title>Jordan Winkler</title>
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
    <link rel="stylesheet" type="text/css" href="""+'"'+css+'"'+""">
 </head>

<body>
 <div id="nav_bar">
  <div id="nav_bar_ul">
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+home+'"'+""">Home</a>
    </div>
   </div>
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+research+'"'+""">Research</a>
    </div>
   </div>
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+courses+'"'+""">Course Notes</a></li>
    </div>
   </div>
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+blog+'"'+""">Blog</a>
    </div>
   </div>
  </div>
 </div>
"""
# }}}
# note_bar
# {{{
def note_bar (css, home, name, back, nexts, up) : 
    bar = """
<!DOCTYPE html PUBLIC "-//w3c//dtd html 5.0 transitional//en">
<html>
 <head>
   <title>Jordan Winkler</title>
   <link rel="stylesheet" type="text/css" href="""+'"'+css+'"'+""">
 </head>

<body>
 <div id="nav_bar">
  <div id="nav_bar_ul">
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+home+'"'+""">"""+name+"""</a>
    </div>
   </div>"""
    if back != None :
        bar += """
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+back.name+'.html"'+""">Back: """+back.name+"""</a>
    </div>
   </div>"""
    if nexts != None :
        bar += """
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+nexts.name+'.html"'+""">Next: """+nexts.name+"""</a></li>
    </div>
   </div>"""
    if up != None :
        bar += """
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+up.name+'.html"'+""">Up: """+up.name+"""</a>
    </div>
   </div>
  </div>
 </div>
"""
    return bar
# }}}
# update
# {{{
update = """
  <div id=update_bar> 

    <p align="center"> <font size="-1">
     Compiled: """ + os.popen('date').read() + """
        </font> </p>
  </div>    
 </body>
</html>
"""
# }}}

# em
#{{{
# topic head
#{{{
em = Page('Electromagnetism', """
<br>
<b>Books</b>
<br><a href="Griffiths/Griffiths.html">Griffiths</a>
 <br>
 <br>
 <br>
<a href="
https://raw.githubusercontent.com/meatyhams/Eel/main/jordans-notes.txt
         ">
  git form of these notes
</a>
<br>
<a href="
https://colab.research.google.com/drive/1xnftEDtCWRNzep3NTsGI1UcFvopYw75o#scrollTo=IBS1-c8nAbnL
         "
  >
  colab python simulation
</a>
<br>
<a href="
https://github.com/meatyhams/Eel
         "
  >
  github
</a>
<br>
<a href="
https://www.maxwells-equations.com/
         "
  >
  Maxwell's equations, the website
</a>
<br>
<a href="
http://danfleisch.com/maxwell//
         "
  >
  Maxwell's equations, a guide by students
</a>
""", next={})
#}}}

# griffiths (in construction)
griffiths = Page('Griffiths','Under construction')
# {{{
def make_book() :
    gr = [Page('grif')] * 20
    griffiths.data = """
    <h3> Electrodynamics Griffiths 4th ed </h3>
    <a href="Griffiths/Preface.html">Preface</a>"""
    for i in range(1,13) :
        griffiths.data += ("<br><a href="
                +griffiths.name+'/'
                +gr[i].name+".html>"
                +gr[i].name+"</a>\n")
    griffiths.data += '</div>'
    griffiths = em.next
    
    # book head
    griffiths.up = em
    ## Make chapters
    for i in range(0,13) :
        gr[i] = {}
    griffiths.next = gr[0]
    ## Make chapter names
    gr[0].name = 'Preface'
    for i in range(1,13) :
        gr[i].name = 'Chapter_'+str(i)
        
        # create tree links
    for i in range(1,13) :
        gr[i].prev = gr[i-1]
    for i in range(1,13) :
        gr[12-i].next = gr[12-(i-1)]
    for i in range(0,13) :
        gr[i].up = em
    
    # create data
    for i in range(0,13) :
        gr[i].data = ''
    gr[0].data = """
    <b>Preface</b>
    <br>
    <br>
    <b>Note to the reader</b>: The first chapter is meant to be a review of the language used to explain electrodynamics, not an explanation of foundations. Attention should be paid to how words are defined, but any metaphysical or logical arguments should be observed with a critical mind. Griffiths is unconnected with work outside of electromagnetism and particle physics, and consumed uncritically the teachings of his predecessors. No offense was meant to professionals of adjacent fields, probably.
    """
    gr[1].data = """
    <h4> Chapter 1: Mathematical Language </h4>
Differential Geometry (vectors, derivatives, integrals, coordinate systems, fields)
<br>
<br>
The potentially easiest way to digest the contents of undergraduate electrodynamics
teaching is via tensors on complex numbers.
<br>
<br>
There are a few levels to think about tensors
<br>
- as defined in the book (physical)
<br>
- via the common category definition (common in algebra)
<br>
- as a model (the fullest definition that allows automated reasoning)
<br>
<br>
In the book a tensor is n x m x o product of numbers. The design is to carry physical information along calculus like transformations. Tensors in this definition also work to make sure type information (units with some measure) carries. They are tedious to write. (and they make you sound uncultured math-wise). Instead these can be typed into python under the differential geometry library in sympy.

<br>
Odd Definitions (Dirac delta, Tensors, etc...)
<br>
<br>
Dirac delta exists as a function in the modern definition. But the textbook definition is to make integral equations easier to bypass.
<br>
<br>
The topological definition of continuity is kind of different than the physical one. I think on the discrete topology all elements are continuous. 

Discussion points:
<br>
<br>

- What is the idea behind electric charge? Was it part of the field theory that
  Maxwell was thinking of? What was the experiment used to demonstrate it? What
other properties does it predict? I am guessing push and pull of magnets led to
the idea.
<br>
<br>
- Is it really true that A dot B = 0 if A and B are perpendicular? Without
  |A||B|cos(theta), it would need some more work to show this to be true. Seems
like a complex analysis thing.
<br>
<br>

- Dot and cross product are kind of physical too. Like do these equations hold
  in a different metric space? Would they hold without a metric? They do not
hold on general vectors, only really on 2d and 3d ones.
<br>
<br>

- Dot and cross products have a nice set up of
  A dot B = |A||B|cos(theta), A cross B = |A||B|sin(theta) n
  Is this part of the design of the two operators?
<br>
<br>

- The cross product is not associative, but the composition of functions is.
  Why? Seems like composition is not defined for 2-arity functions. This has
kind of an odd property to it.
<br>
<br>

- A . (B x C) is the volume of a parallelpiped. BAC-CAB rule exists. Lots of
  computational shorthand. It kind of reminds me of old statistics books before
computers were invented. I can see it being a nice shorthand for being a
chalkboard-bounded physicist. But it seems like a bit much to mentally maintain
as a computational physicist, right?
<br>
<br>

- 1.31 is verbose. But the notation is nice and concise for describing 3d
  rotation. Quaternions could also work here I think.  b = Ax would have been
much less tedious too. In computing I would have just wrote out a function
definition for this special case though. And in higher level math that is also
what you would do,
<br>
<br>

- Differential geometry is a weird subject. It takes many of these unusual
  operators and runs with it. I think this is due to how interesting these
operators are geometrically. How did your general relativity class merge math
and physics versions of these objects?
<br>
<br>

- Why does the gradient point towards greatest descent? Looks like component
  derivatives. So it is going for the taxi metric sum of velocity.
<br>
<br>

- gradient, divergence, and curl are just functors. There is a more essential definition under them I think.
<br>
<br>

- gradient seems like it was thrown together. I don't get its design. But
  divergence and curl are actually kind of interesting. They split derivatives
on vectors into two familiar components seen in complex analysis: scale and
rotation of a+bi.
<br>
<br>

- Most of the 1.2.6 identities directly follow from elementary algebra
  identities. Seems kind of excessive to mention them.
<br>
<br>

- page 23 has the Laplacian. 
<br>
<br>


I am really curious how this stuff works in complex analysis, and a little in
differential geometry. DG is kind of a foil for physics, so it is probably
going to look a lot like its physical counterpart. But CA could give some weird
extra information about what is being said in this book. Possible computational
speedups because it is so polynomial-based.
<br>
<br>

Line integrals are surprisingly deep. Ch 1.5 and 1.6 look interesting and new to me. 
<br>
<br>

Overall, I have a feeling only a fraction of the math used in the intro is actually needed to work with EM. And the math is a bit dated.
<br>
<br>
    """
#}}}

# summer_of_logic
# {{{
summer_of_logic = Page('summer_of_logic',"""
<p><b>Summer of Logic</b></p>

All things logic 10 hours a day for 100 days.

Reading research papers, coding in dependent type theories, and reviewing logic books.
<br>
<br>
I also took some time doing random things: trying to start a workshop on
symbolic AI, learning about the electromagnetic force.

</td></tr></tbody></table> </p> </p> </center> <hr>
Notes:
<br>

<br>
 <a href="
          pl.html
         "
    target="_top">
 </a>
        Programming Language Theory

<br>
 <a href="
          tt.html
         "
    target="_top">
 </a>
        Type theory
<br>
 <a href="
          topology.html
         "
    target="_top">
        Topology
 </a>
<br>
 <a href="
          Electromagnetism/Electromagnetism.html
         "
    target="_top">
        Electromagnetic force
 </a>


</td></tr></tbody></table></p></p></center><hr>

Stuff I found:
<br>
<br>
Programming language theory/practice
<br>
 <a href="
https://www.amazon.com/dp/012088478X/
         "
    target="_top">
Art of compiler making stuff (book)
 </a>
<br>
 <a href="
https://www.cs.purdue.edu/homes/bendy/cs565/fall20/index.html#logistics
         "
    target="_top">
CS 565 Programming Languages (fall)
 </a>
<br>
 <a href="
cs565-spring2020/index.html
         "
    target="_top">
CS 565 Programming Languages (spring)
 </a>
<br>
 <a href="
https://6826.csail.mit.edu/2020/
         "
    target="_top">
Coq course (MIT: based on Upenn)
 </a>
<br>
 <a href="
https://softwarefoundations.cis.upenn.edu/
         "
    target="_top">
        Software Foundations
 </a>
<br>
<a href="
https://www.cs.cmu.edu/~rwh/pfpl/
">
Practical foundations to programming languages (type theory+PL)
</a>
<br>
 <a href="
https://www.cs.princeton.edu/~appel/papers/plcc.pdf
         "
    target="_top">
Program Logics for Verified Compilers
 </a>
<br>
<br>
Type Theory
<br>
 <a href="
https://ncatlab.org/nlab/show/type+theory
         "
    target="_top">
         nlab type theory
 </a>
<br>
 <a href= "
Programming-in-Martin-Löfs-Type-Theory.pdf
    "
    target="_top">
        Classic intuinistic type theory (free book)
 </a>
<br>
 <a href= "
    https://www.youtube.com/playlist?list=PL1-2D_rCQBarjdqnM21sOsx09CtFSVO6Z
    "
    target="_top">
        Homotopy Type Theory (course)
 </a>
<br>
 <a href= "
hott-online-1287-g1ac9408.pdf
    "
    target="_top">
        Homotopy Type Theory (free book)
 </a>
<br>
 <a href="
https://favonia.org/courses/hdtt2020/
         "
    target="_top">
         Cubical Type Theory (course)
 </a>

<br>
<br>
Algebraic Topology 
<br>
 <a href="
          https://ncatlab.org/nlab/show/Introduction+to+Topology
         "
    target="_top">
algebraic topology (nlab book)
 </a>

<br>
 <a href="
https://www.amazon.com/dp/0521795400/
         "
    target="_top">
algebraic topology (book)
 </a>
<br>
 <a href="
https://youtube.com/playlist?list=PLpRLWqLFLVTCL15U6N3o35g4uhMSBVA2b
         "
    target="_top">
         algebraic topology (course lectures)
 </a>
<br>
 <a href="
          https://www.youtube.com/channel/UCLJWRcHW-mjDSbpkIX6B-cw
         "
    target="_top">
         Purdue Topology (research lectures)
 </a>

<br>
<br>
Mathematical Logic
<br>
 <a href="
https://www.amazon.com/Introduction-Mathematical-Discrete-Mathematics-Applications/dp/1482237725/
         "
    target="_top">
Mathematical Logic (book)
 </a>
<br>
 <a href="
https://www.amazon.com/Philosophy-Model-Theory-Tim-Button/dp/0198790406/
         "
    target="_top">
         philosophy of model theory (book)
 </a>
<br>
 <a href="
https://www.amazon.com/Combinatorial-Set-Theory-Introduction-Mathematics/dp/1447121724
         "
    target="_top">
Combinatorial Set Theory (book)
 </a>
        <br>
        <br>
<b>How it all combines</b>
        <br>
        <a href="
        https://ncatlab.org/nlab/show/computational+trilogy
        ">
                proofs = programs = spaces
        </a>
        <br>
        <br>
<br>
<br>
Journals and other
<br>
 <a href="
https://engineering.purdue.edu/~xqiu/ece663/references/References.html
         "
    target="_top">
formal methods books and papers
 </a>
<br> 
<a href=" http://csrankings.org/#/index?&plan&log&world "
   target="_blank"
        >source of research papers (CS: language+logic)</a>
<br> 
<a href="
https://www.cambridge.org/core/journals/journal-of-symbolic-logic/listing?q=&searchWithinIds=56ED3BA46977662562A26BC04DD604FD&aggs[productTypes][filters]=JOURNAL_ARTICLE
"
   target="_blank"
   >Journal of Symbolic Logic
</a>

<br>
<br>
Cool logic groups
<br>
<a href="
http://www.logic.cmu.edu/index.html
">
        pure and applied logic (CMU)
</a>
<br>
<a href="
https://github.com/coq-community/manifesto
">
Coq community
</a>
<a href="
https://arxiv.org/about/reports/submission_category_by_year
">
</a>
""")
# }}}

topology = Page('topology',"""

I found a bunch of books on the subject. But what really stands out is this formalization in calculus of inductive constructions.

<br>
<a href="../../data/topology">coq topology</a>
        """)

# blogs, these should be generated from files
# {{{

# started (Jul 12 2021)
blogs = get_blogs(blogs_source)
# blog
# {{{
blog = Page('blog',"""
 <b>Advice an old me needed, and a newer me might find foolish</b>
<br>
<br>
""")
for i in range(len(blogs)) :
    blog.data += listlink(blogs[i].name.replace('_',' '), blogs[i].name+'.html')

# }}}

#}}}

# courses
# {{{
courses = Page('courses',"""
<p><b>Spring 2021</b></p>

<p>
ECE 595 Machine Learning
<br>
ECE 600 Random Variables and Signals
<br>
ECE 662 Pattern Recognition and Decision Making

<p><b>Fall 2021</b></p>

<p>
ECE 664 Computability, Complexity, and Languages

<br>
ECE 608 Computational Models and Methods 

<br>
ECE 595 Compilers: optimization, code generation

</td></tr></tbody></table> </p> </p> </center> <hr>

<p><b>Summer 2021 </b></p>

<p>
"""+lname('Summer of Logic',
    'summer_of_logic/summer_of_logic.html')+"""

</td></tr></tbody></table> </p> </p> </center> <hr>


<p><b>Spring 2021</b></p>

<p>
 <a href=
        "https://engineering.purdue.edu/~xqiu/ece663/"
    target="_top">
 </a>
        ECE 663 Advanced compilers (applied mathematical logic)

<br>
 <a href=
        "https://engineering.purdue.edu/ECE/Academics/Online/Courses/advanced-software-engineering"
    target="_top">
 </a>
        ECE 595 Advanced Software Engineering

<br>


<p><b>Fall 2020</b></p>

<p>
MA  598 Set Theory
<br>
MA  585 Mathematical Logic
<br>
ECE 595 Intro to Compilers
""")
# }}}

# research
# {{{
research = Page('research',"""
 <h2>Research Interests</h2>
  <p>
Logic; the <a href="https://en.wikipedia.org/wiki/Language_game_(philosophy)">language-game</a> of precision, consistency, and world building. Working in logic can mean working in such fields as: philosophy, mathematics, computer science, and linguistics.
  </p>

  <p>In particular:</p>
   <ul>
    <li><b>Type Theory</b>: A grand unified theory of computation. Types classify constructions.
    </li>
<br>
<li><b>Model Theory</b>: 
A discipline that is similar to the set of tools <a
href="http://www.classicallibrary.org/descartes/meditations/">Descartes</a>
would have used. Models sit on top of symbolic logic, and bear many
similarities to algebraic geometry. They are the instances of programs, and the
living breathing citizens of logical universes. Useful in <a href="
                https://www.amazon.com/Philosophy-Model-Theory-Tim-Button/dp/0198790406/
                ">Philosophy</a>,  
        and 
        <a href="
           https://en.wikipedia.org/wiki/Finite_model_theory
                ">Computer Science</a>.
</li>
<!--
<br>
<li><b>Algebraic Topology</b>: Generally softer geometric equalities and
structures. Topologies can be used to do things normally done with a logic,
such as defining spaces for mathematical analysis to work.

</li>
<br>
<li><b>Algebraic Geometry</b>: 
Multivariate polynomials, and structures defined as solutions to a larger
series of equations. The magic (for me at least) of having a solution to an
equation is a popular theme in algebraic geometry. Looking into 
<a
href="
      https://www.math.uwaterloo.ca/~snburris/htdocs/MAL.pdf
">The Mathematical Analysis of Logic</a> you will find that the original
Boolean Algebra, the first logical species of mathematical structures, was
defined more as systems of equations, than the common operator based structure
found today in undergraduate texts.  

</li>
-->

<!--
<br>
<li><b>Constructive Mathematics</b>: 
Mathematics is grand, powerful, and even beautiful. But, I am not gullible, or
desperate for just any mathematics teaching job. So I can take my time, be more
constructive, and more intuitive about mathematical discoveries. Constructive
methods are more dependable, simple to verify, and translate between logics, or
into programs. 

-->
<br>
<li><b>Verification of programs</b>: 
What's it all about? It is about an approach to bringing software engineering
up to speed with more traditional engineering disciplines, providing a
mathematical foundation for rigorous analysis of realistic computer systems. As
civil engineers apply their mathematical canon to reach high certainty that
bridges will not fall down, the software engineer should apply a different
canon to argue that programs behave properly. As other engineering disciplines
have their computer-aided-design tools, computer science has proof assistants,
IDEs for logical arguments. We can learn how to apply these tools to certify
that programs behave as expected.
</li>
<br>
<li><a href="https://barghouthi.github.io/2017/04/24/synthesis-primer/"></a>
<b>Synthesis of programs</b>: 
The study of how to use language to generate programs. At highest reliability,
such a language is a logic. But this discipline encompasses what compilers can
generate from a given language, and what a machine learning program can do
based on its specification.
</li>
 </ul>

 </p>
 
</td></tr></tbody></table> </p> </p> </center> <hr>

<h2>Research Done</h2>

<ul>
 <li><a href="
https://github.com/PurdueDualityLab/deepbugs-jr
    "
    target="_top">
Reproduction of ``DeepBugs: A Learning Approach to Name-based Bug Detection''
 </a> (May 2021)
 </li>
 <br>
<li> <a href="
              https://github.com/Jmw150/Brain-Generator
    "
    target="_top">
BrainGan: A brain (deep neural net) that makes pictures of brains
 </a> (Dec 2019)
    </li>
</ul>

</td></tr></tbody></table> </p> </p> </center> <hr>

<h2>Projects</h2>

See <a href="https://github.com/jmw150" target="_blank" >github</a>.
""")
#}}}

# home (index)
# {{{
home = Page('index',"""
<div id="title">
 <font face="Albertus Medium">
  <h2><i>Jordan Winkler</i></h2>
  <h3>Logician, Computer Scientist </h3>
 </font>
</div>

<div id="upper_square">
 <br>
 <center>
    <img src="data/JordanWinkler.jpg" height="270" align="middle">
 </center>
</div>
<div id="lower_square">
 <p>
  <a href="https://github.com/jmw150" target="_blank" >github</a>,
  <a href=" https://qoto.org/web/accounts/373087 " target="_blank" >mastodon</a>,
  <a href="https://twitter.com/JordanWinkler1" target="_blank" >twitter</a>,
  <a href="https://www.linkedin.com/in/jordan-winkler-65254283/" target="_blank" >linkedin</a>,
  <a href="data/JW_resume.pdf">CV</a>
</div>
""")
# }}}

#}}}

#}}}

def write_file(file, content):
    f = open(file+'.html', "w")
    f.write(content)
    f.close()

def build_page(content,path='') :

    ln = path.split('/')
    level = len(ln)-1
    file = content.name

    # handle file generation of content
    if level > 0 :
        ls = ln[0]
        if not os.path.exists(ls) :
            os.mkdir(ls)
        for i in range(1,level) : # skip last 
            ls += '/'+ln[i]
            if not os.path.exists(ls) :
                os.mkdir(ls)
        file = ls +'/'+ content.name

    ab = '../'*level

    write_file(file,
            (nav_bar(
                ab+css,
                ab+home_path,
                ab+research_path,
                ab+course_path,
                ab+blog_path)
                +'<div id="content">'
                +content.data
                +'</div>'
                +update))

# wiki book style
def build_book(level:int, chapter:int, file_base:str, content:dict) :

    # exit base case
    if content == None :
        return 

    # recursion case
    ab = '../'*level
    write_file(file_base+'/'+content['name']+'.html',
            (note_bar(
                ab+css,
                ab+home_path,
                content['name'],
                content['prev'],
                content['next'],
                content['up'])
                +'<div id="content">'
                +content['data']
                +'</div>'
                +update))

    # and then recursion
    ## across
    if chapter >= 0 :
        build_book(level,chapter-1,file_base,content['next'])
    else:
    ## down
        build_book(
                level+1, 
                12, # for example
                file_base+'/'+content['name'], 
                content['next'])

def build_site() :
    build_page(home)

    build_page(courses,'courses/')
    build_page(summer_of_logic,'courses/summer_of_logic/')
   
    build_page(em,'courses/summer_of_logic/'+em.name+'/')
    build_page(griffiths,'courses/summer_of_logic/'+em.name+'/'+griffiths.name+'/')

    build_page(topology,'courses/summer_of_logic/'+topology.name+'/')

    build_page(blog,'blog/')
    for i in range(len(blogs)) :
        build_page(blogs[i],'blog/')

    build_page(research,'research/')

def main() :
    build_site()

main()

