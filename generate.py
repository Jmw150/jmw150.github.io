# A python script to generate websites
# Jordan Winkler

# algs
#{{{
import time 
import os
from typing import * # List, etc..

# subclass of Page
class Tag:
    def __init__(self, name, nickname='') :

        # name is the location
        self.name = name
        if nickname == '':
            self.nickname = name
        else:
            self.nickname = nickname

    # for adding path elements (../) and file types (.html)
    def __add__(self, y) :
        return Tag(str(self.name) + str(y), self.nickname)
    def __radd__(self,y) :
        return Tag(str(y) + str(self.name), self.nickname)

    def __str__(self):
        return str(self.name)
    def __repr__(self):
        return str(self.name)

# Paths
#{{{
blogs_source = '../../blog'
## for defaults in Page
css = Tag('bluestyle.css')
data = Tag('data')
#}}}

class Page (Tag):
    #{{{
    "A website page"
    def __init__(self, name, data=' ', nickname= '', nav=[], cleanable=True):
        self.name = name
        if nickname == '':
            self.nickname = name
        else:
            self.nickname = nickname
        self.data = data
        self.cleanable = cleanable

        # default stuff
        home = Tag('index', nickname='Home')
        research = Tag('research/research',nickname='Research')
        courses = Tag('courses/courses', nickname='Courses')
        blog = Tag('blog/blog', nickname='Blog')

        # extra possible metadata
        if nav == [] : 
            self.nav = [home,research,courses,blog]
        else :
            self.nav = nav

    # this is odd design, Python
    def __add__(self, y) :
        if type(y) == Page :
            return Page(self.name, str(self.data) + str(y.data), 
                    self.nickname, self.nav, self.cleanable)
        else :
            return Page(self.name, str(self.data) + str(y), 
                    self.nickname, self.nav, self.cleanable)

    def __radd__(self,y) :
        if type(y) == Page :
            return Page(self.name, str(self.data) + str(y.data), 
                    self.nickname, self.nav, self.cleanable)
        else :
            return Page(self.name, str(self.data) + str(y), 
                    self.nickname, self.nav, self.cleanable)

    # looks like a path variable
    def __truediv__(self, y='/') : # doesn't matter, a/ is still a syntax error
        if type(y) == Page :
            return Page(str(self.name) + '/' + str(y.name), 
                self.data, self.nickname, self.nav, self.cleanable)
        else :
            return Page(str(self.name) + str(y), 
                self.data, self.nickname, self.nav, self.cleanable)


    def __rtruediv__(self, y) :
        if type(y) == Page :
            return Page(str(y.name) + '/' + str(self.name), 
                self.data, self.nickname, self.nav, self.cleanable)
        else :
            return Page(str(y) + str(self.name), 
                self.data, self.nickname, self.nav, self.cleanable)
    
    # get data, also process data
    def dat(page, size=2) : # size might be another property to add
        
        if page.cleanable == True :
            # double enter -> html 
            data = page.data.replace('\n\n','<br><br>\n') 
        
            s = str(size)
    
            # add title
            page.data = '\n<h'+s+'>'+page.nickname.replace('_',' ').title()+'</h'+s+'>\n'
            page.data += data
    
            page.cleanable = False
            # TODO: evaluate links in data

        return page.data

#}}}

# html macros
link = lambda page : '<br><a href='+page.name+'/'+page.name+'.html>'+page.nickname+'</a>'
inlink = lambda page : '<a href='+page.name+'/'+page.name+'.html>'+page.nickname+'</a>'
exlink = lambda page : '<br><a target="_blank" href='+page.name+'>'+page.nickname+'</a>'
link_here = lambda page : '<br><a href='+page.name+'.html>'+page.nickname+'</a>'
bar = lambda : '</td></tr></tbody></table></p></p></center><hr>'

def get_file(filename) :
    File = ""
    with open(filename) as f:
        for l in f.readlines() :
            File += l

    return File

def get_blogs(path:str) -> List[Page]:

    # get blog list at location
    bloglist = os.popen('ls -t '+path).read().split('\n')[:-1]

    blogs = []
    # add title to work, and clump together
    for i in bloglist :
        file = get_file(path+'/'+i)
        file = str(Page(i,file).dat())
        blogs.append(Page(i,file,cleanable=False))
    
    return blogs

def write_file(file, content):
    f = open(file+'.html', "w")
    f.write(content)
    f.close()

def build_page(content,path='') :

    ln = str(path).split('/')
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

    # set absolute path to nav
    for i in range(len(content.nav)) :
        content.nav[i].name = ab+content.nav[i].name

    write_file(file,
                nav_bar(ab/css, content.nav)
                +'<div id="content">'
                +content.dat()
                +'</div>'
                +update.data)

#}}}

# forward declare web pages, so they can talk about each other
#{{{
css = Page('bluestyle.css', cleanable=False)
data = Page('data', cleanable=False)
home = Page('index', nickname='Home', cleanable=False)
courses = Page('courses', nickname='Courses', cleanable=False)
research = Page('research', nickname='Research', cleanable=False)
blog = Page('blog', nickname='Blog', cleanable=False)

summer_of_logic = Page('summer_of_logic',nickname='Summer of Logic',cleanable=False)
pl = Page('programming_languages',nickname='Programming Language Theory')
tt = Page('type_theory',nickname='Type Theory')
topology = Page('topology',nickname='Topology')
em = Page('Electromagnetism',nickname='Electromagnetic Force')
griffiths = Page('Griffiths')

ml = Page('machine_learning',nickname='ECE 595 Machine Learning')
probability = Page('probability',nickname="ECE 600 Random Variables and Signals")
stat_pattern = Page('stat_pattern', nickname='ECE 662 Pattern Recognition and Decision Making')

# This fall
ccl = Page('ccl', nickname='ECE 664 Computability, Complexity, and Languages')
algorithms = Page('algorithms', nickname='ECE 608 Computational Models and Methods')
compilers = Page('compilers', nickname='ECE 595 Compilers: optimization, code generation')
## books
ccl_book = Page('ccl_book', nickname='The Book')
random_graphs = Page('random_graphs', nickname='Random Graphs')
comp_intract = Page('comp_intract', nickname='Computers and Intractability')
algorithms_book = Page('alg_book', nickname='Introduction to Algorithms')
engineer_compiler = Page('eng_compiler', nickname='Engineering a Compiler')
antlr_reference = Page('antlr', nickname='ANTLR Reference Book')

adv_compilers = Page('adv_compilers',nickname='ECE 663 Advanced compilers')
se = Page('software_engineering',nickname='ECE 595 Advanced Software Engineering')

set_theory = Page('set_theory',nickname='MA  598 Set Theory')
math_logic = Page('mathemetical_logic',nickname='MA  585 Mathematical Logic')
intro_compilers = Page('intro_compilers',nickname='ECE 595 Intro to Compilers')
#}}}

# interconnected parameters
#{{{
# navigation bar needs another entry
pl.nav.append(Page('courses/summer_of_logic/summer_of_logic',nickname='SoL'))
tt.nav.append(Page('courses/summer_of_logic/summer_of_logic',nickname='SoL'))
topology.nav.append(Page('courses/summer_of_logic/summer_of_logic',nickname='SoL'))
em.nav.append(Page('courses/summer_of_logic/summer_of_logic',nickname='SoL'))

ccl_book.nav.append(Page(str(courses/ccl/ccl),nickname='CCL'))
random_graphs.nav.append(Page(str(courses/ccl/ccl),nickname='CCL'))
comp_intract.nav.append(Page(str(courses/ccl/ccl),nickname='CCL'))

#}}}

# web data
#from data.data import *
#{{{
# navigation bar (nav_bar)
#{{{
def nav_bar (css, args) :
    bar = """
<!DOCTYPE html PUBLIC "-//w3c//dtd html 5.0 transitional//en">
<html>
 <head>
   <meta name="viewport" content="width=device-width">
   <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
   <title>Jordan Winkler</title>
   <link rel="stylesheet" type="text/css" href="""+'"'+css.name+'"'+""">
 </head>

<body>
 <div id="nav_bar">
  <div id="nav_bar_ul">"""
    for i in args :
        if type(i) == str :
            i = Page(i)
        bar += """
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+i.name+'.html"'+""">"""+i.nickname+"""</a>
    </div>
   </div>"""
    bar += """
  </div>
 </div>
"""
    return bar
#}}}

# update (the time-stamp at the bottom of each web page)
#{{{
update = Page('update',"""
  <div id=update_bar> 
   <p align="center">
    <font size="-1">
     Compiled: """ + os.popen('date').read() + """
    </font>
   </p>
  </div>    
 </body>
</html>
""")
#}}}

# blog
#{{{
blogs = get_blogs(blogs_source) # started (Jul 12 2021)
blog.data = """ 
<!-- <b>I drink and I know things</b> -->
<b>He just keeps talking...</b>
<br>
<br>
"""
for i in range(len(blogs)) :
    blog.data += link_here(blogs[i])
#}}}

# research
#{{{
research = Page('research',"""
 <h2>Research Interests</h2>
 <p>
<b>Logic</b>: the <a href="https://en.wikipedia.org/wiki/Language_game_(philosophy)">language-game</a>
of precision, consistency, and world building. Working in logic can mean
working in such fields as: philosophy, mathematics, computer science, and
linguistics.  
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
    target="_blank">
Reproduction of ``DeepBugs: A Learning Approach to Name-based Bug Detection''
 </a> (May 2021)
 </li>
 <br>
<li> <a href="
              https://github.com/Jmw150/Brain-Generator
    "
    target="_blank">
BrainGan: A brain (deep neural net) that makes pictures of brains
 </a> (Dec 2019)
    </li>
</ul>

</td></tr></tbody></table> </p> </p> </center> <hr>

<h2>Projects</h2>

See <a href="https://github.com/jmw150" target="_blank" >github</a>.
""", cleanable=False)
#}}}

# home (index)
#{{{
home.data = """
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
"""
#}}}

# other
#{{{
ml.data = """
<b>motivation:</b> Its one of the cooler parts of AI

<b>personal note:</b> As of writing this, I am a machine learning scientist. (yay) 
I hope I get Chan for this topic though. His course covers convex optimization
and a bunch of more mathematical aspects of machine learning. Having a healthy
career in a topic means building a good foundation.  

https://engineering.purdue.edu/ChanGroup/ECE595/
"""

stat_pattern.data = """
<b>motivation:</b> Statistical patterns is a topic categorized along with
computer vision in research 
"""

probability.data = """
<b>motivation:</b> Signals are an interesting aspect of system engineering. Combine it with electrodynamics, and you have physical computation on almost anything.
"""
#}}}

compilers.data = """
<b>motivation:</b><br>
- Optimization in compilers technology is where most practical use of algorithms is found. Algorithms is <br>
- Code Generation in compiler tech leads into the far more impressive field of program synthesis
"""+bar()+"""
"""+(
inlink(engineer_compiler)+
link(antlr_reference)
        )+"""
"""

ccl.data = """
<b>Motivation:</b> <br>
<ul>
    <li><b>Computability</b>: In this case naive computability. For computer scientists it is the limitations of Turing machines (f : Nat -> Nat), which is arguably not as useful as it sounds. For mathematicians it is called recursion theory and it is more about paradoxes.
 </li>
    <li><b>Complexity</b>: In this case probably classical complexity. Complexity is about search spaces of (f : Nat -> Nat) phrased as problems. "Machine Learning" deals in functions on higher dimension, larger search spaces. So, despite what the professor for this class says, classical complexity is less relevant (if not incorrectly applied) on algorithms that handle larger spaces.
 </li>
    <li><b>Languages</b>: An area of programming all CS people should learn, because it unlocks the real potential in programming.
 </li>
</ul>
"""+bar()+"""
<a href="
https://engineering.purdue.edu/kak/ComputabilityComplexityLanguages/Index.html"
   target="_blank"
>Course Content</a>

"""+(
inlink(ccl_book)+
link(comp_intract)+
link(random_graphs)
        )+"""

<b>Scrolls</b><br>
Why Study Computability, Complexity, and Languages?
<br>
- This section is on motivating topics of the course. It is easy to sell me on most of his points, as I do not find being well-read to be a major crime against professional productivity.

Mathematical Prerequisites <br>
- Beautiful stuff. The notation for first order logic is the familiar stuff from first semester Mendelson. <br>
- The guy is a Python programmer. I guess that makes sense for being a deep learning guy.

<b>Questions</b><br>
- computability limitations versus type theory lack of limitations. (probably representation misnomer) <br>
- Robot intelligence will not exceed human intelligence?

Off of the top of my head, the last is a weak argument on 2 accounts: <br>
(1.) Finite navigation over large infinite terrain is physical about the terrain,
not the navigation method. Ex. Having a library on methods versus inventing
from scratch. Deep learning is this on inherent topological structures in
reality.

(2.) Computable is smaller than representable. Infinite structures can be described
and manipulated concretely with finite descriptions and morphisms. There are
limits to representation as well. But this is an argument against Turing
machines as a limitation on computation.  
"""

ccl_book.data = """
    
"""
comp_intract.data = """

"""
random_graphs.data = """

"""

algorithms.data = """
<b>motivation:</b><br>This class will cover less trivial algorithms to use analytical number theory on.
"""+bar()+"""
I would like to get topology settled mentally, before doing this analytic number theory based song and dance.

Here is the 
<a href="
https://engineering.purdue.edu/~pomeranz/ECE608/ECE608_distance.pdf"
   target="_blank"
>syllabus</a>. And here are notes on the books used.
"""+(
link(algorithms_book)+
link(comp_intract)
)+"""

"""

# summer
#{{{
summer_of_logic.data = """
<p><b>Summer of Logic</b></p>

<a href="
https://www.cambridge.org/core/journals/journal-of-symbolic-logic/listing?q=&searchWithinIds=56ED3BA46977662562A26BC04DD604FD&aggs[productTypes][filters]=JOURNAL_ARTICLE
"
   target="_blank">
<img src="../../data/ASL_logo.png" height="50">
</a>
<br>
<br>
All things logic 10 hours a day for 100 days.

Reading research papers, coding in dependent type theories, and reviewing logic books.
<br>
<br>
I also took some time doing random things: trying to start a workshop on
symbolic AI, learning about the electromagnetic force, trying to get my fairly
derivative research published, and making this website.

"""+bar()+"""
Notes:
<br>"""+(
link(pl) +
link(tt) +
link(topology) +
link(em)) + """

"""+bar()+"""

Stuff I found:
<br>
<br>
<b> Mathematical Logic </b>
<br>
 <a href="
https://www.amazon.com/Introduction-Mathematical-Discrete-Mathematics-Applications/dp/1482237725/
         "
    target="_blank">
Mathematical Logic (book)
 </a>
<br>
 <a href="
https://www.amazon.com/Philosophy-Model-Theory-Tim-Button/dp/0198790406/
         "
    target="_blank">
         philosophy of model theory (book)
 </a>
<br>
 <a href="
https://www.amazon.com/Combinatorial-Set-Theory-Introduction-Mathematics/dp/1447121724
         "
    target="_blank">
Combinatorial Set Theory (book)
 </a>
        <br>
        <br>
<b>How it all combines</b>
        <br>
        <a href="
        https://ncatlab.org/nlab/show/computational+trilogy
        "> proofs = programs = spaces </a>
<br>
<br>
<b>
Journals and other
</b>
<br>
 <a href="
https://engineering.purdue.edu/~xqiu/ece663/references/References.html
         "
    target="_blank">
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
<b>
Cool logic groups
</b>
<br>
<a href="
http://www.logic.cmu.edu/index.html
">
        pure and applied logic (CMU)
</a>
<br>
<a href="
https://www.cs.purdue.edu/homes/roopsha/purform/projects.html
">
        Purdue formal methods (PurForm)
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
"""

tt.data = """
So far the major source of effort has been in using Coq with HoTT, and using Coq in general.

I found some stuff

 <a href="
https://ncatlab.org/nlab/show/type+theory
         "
    target="_blank">
         nlab type theory
 </a>
<br>
 <a href= "
Programming-in-Martin-Löfs-Type-Theory.pdf
    "
    target="_blank">
        Classic intuinistic type theory (free book)
 </a>
<br>
 <a href= "
    https://www.youtube.com/playlist?list=PL1-2D_rCQBarjdqnM21sOsx09CtFSVO6Z
    "
    target="_blank">
        Homotopy Type Theory (course)
 </a>
<br>
 <a href= "
hott-online-1287-g1ac9408.pdf
    "
    target="_blank">
        Homotopy Type Theory (free book)
 </a>
<br>
 <a href="
https://favonia.org/courses/hdtt2020/
         "
    target="_blank">
         Cubical Type Theory (course)
 </a>
"""

pl.data = """

So far, lots and lots of compiler theory. But also basic Coq can be found here.

 <a href=" https://www.amazon.com/dp/012088478X/ "
    target="_blank">
Art of compiler making stuff (book)
 </a>
<br>
 <a href="
https://www.cs.purdue.edu/homes/bendy/cs565/fall20/index.html#logistics
         "
    target="_blank">
CS 565 Programming Languages (fall)
 </a>
<br>
 <a href="
cs565-spring2020/index.html
         "
    target="_blank">
CS 565 Programming Languages (spring)
 </a>
<br>
 <a href="
https://6826.csail.mit.edu/2020/
         "
    target="_blank">
Coq course (MIT: based on Upenn)
 </a>
<br>
 <a href="
https://softwarefoundations.cis.upenn.edu/
         "
    target="_blank">
        Software Foundations
 </a>
<br>
<a href="
https://www.cs.cmu.edu/~rwh/pfpl/
"
    target="_blank">
Practical foundations to programming languages (type theory+PL)
</a>
<br>
 <a href="
https://www.cs.princeton.edu/~appel/papers/plcc.pdf
         "
    target="_blank">
Program Logics for Verified Compilers
 </a>
<br>
<br>

"""

topology.data="""
I found a bunch of books on the subject. But what really stands out is this formalization in calculus of inductive constructions.

<a href="../../../data/topology">coq topology</a>

Aside from that, the meat of topology that is interesting from a logic
perspective is algebraic logic. So this is what I found.  

<b> Algebraic Topology </b><br>
 <a href="
          https://ncatlab.org/nlab/show/Introduction+to+Topology
         "
    target="_blank">
algebraic topology (nlab book)
 </a>
<br>
 <a href="
https://www.amazon.com/dp/0521795400/
         "
    target="_blank">
algebraic topology (book)
 </a>
<br>
 <a href="
https://youtube.com/playlist?list=PLpRLWqLFLVTCL15U6N3o35g4uhMSBVA2b
         "
    target="_blank">
         algebraic topology (course lectures)
 </a>
<br>
 <a href="
 https://math.ucr.edu/home/baez/algebraic_blankology/
         "
    target="_blank">
         algebraic topology (course notes)
 </a>
<br>
 <a href="
          https://www.youtube.com/channel/UCLJWRcHW-mjDSbpkIX6B-cw
         "
    target="_blank">
         Purdue Topology (research lectures)
 </a>


        """
#}}}

# past
# {{{
adv_compilers.data = """
<b>Note</b>: Admittedly, my notes for this entire year are terrible. Everything was online. So I just rewatched parts of lectures if I forgot about something. And the course materials are copyrighted. So I am not allowed to share the main content of what was said or done. Sorry.

    What an amazing, life changing, course. Before this course I was unaware
    that there was money to be made in logic. Formal methods, solvers, and
    program synthesis uses a lot of advanced results in logic.

        "https://engineering.purdue.edu/~xqiu/ece663/"
        """

se.data = """
<b>Note</b>: Admittedly, my notes for this entire year are terrible. Everything was online. So I just rewatched parts of lectures if I forgot about something. And the course materials are copyrighted. So I am not allowed to share the main content of what was said or done. Sorry.
<br>
<br>
    I learned that software engineering is a subset of system engineering.
    System engineering is actually novel. Software engineering before this
    class seemed to be all about middle management of the actual programmers,
    and using mathematical techniques to manage projects better.
<br>
<br>
    This was also a good course in the sense that we read current software
    engineering research articles and I was able to finish some actual
    scientific research in it.
<br>
<br>
        "https://engineering.purdue.edu/ECE/Academics/Online/Courses/advanced-software-engineering"
    """

math_logic.data = """
<b>Note</b>: Admittedly, my notes for this entire year are terrible. Everything was online. So I just rewatched parts of lectures if I forgot about something. And the course materials are copyrighted. So I am not allowed to share the main content of what was said or done. Sorry.
<br>
<br>
I have already taken a philosophical logic (pure-blooded logic) course. So I
may leave out some details, as those are trivial to me.
<br>
<br>
The online offering of Mathematical Logic is why I decided to go to main campus
Purdue for the pandemic of 2020. Purdue often ranking in the single digits in
the US, for engineering disciplines, was cool. But I am only a practical person
to pay the bills.
<br>
<br>
We covered propositional logic for about a week, and the dived into predicate
logic based model theory for 70% of the semester, finally finishing up with
formal number theory and the classic Gödel theorems.
<br>
<br>
Model are an amazing way to talk about mathematics. It is heavy. But this kind
of weight of tools is a good investment when working with high infinity objects
with concreteness. In the class models were treated as sacred and real thing.
But it is really just a design. A model can be pulled out of a logic. Stuff
like separation algebra exists as a model for separation logic.
<br>
<br>
Models are a lot like universal algebra and
algebraic geometry. The professors research subject is even in O-minimality,
which, from my understanding have a lot of connections to some types of
algebraic geometry.  
<br>
<br>
It seems like almost everybody is too gullible to read through Gödel's theorems
before talking about them. So it was nice to have these theorems given full
attention, and understanding of them taken for a grade. They are really very
specific theorems. They kick Hilbert's attempt at converting all of math to
classical number theory. That much I am even grateful for. Elementary number
theory has a just big enough infinity in it to be an inconsistent (or
incomplete) pain in the ass. Going down to finite systems, everything is
provable and consistent, if it was made to be. There are no surprises there.
And, simply taking off the + or * operators is also enough to make a natural
number level system complete. So it is not even that the use of infinity is at
fault. The problem is really in recursion. Pretty much all paradoxes are about self
reference problems. Recursion is one of the 4 big classical fields of
mathematical logic, somewhat due to this I think.
<br>
<br>
Mathematical logic is a giant field. We did not have time for Recursion Theory
or Set Theory. Luckily I took a separate course on at least <a
href="../set_theory/set_theory.html">Set Theory</a> this semester.  
"""

set_theory.data = """
<b>Note</b>: Admittedly, my notes for this entire year are terrible. Everything was online. So I just rewatched parts of lectures if I forgot about something. And the course materials are copyrighted. So I am not allowed to share the main content of what was said or done. Sorry.
<br>
<br>
This class started from the foundations of set theory as they were talked about historically. 
<br>
<br>
The main insight I gathered from set theory is that of the classical
mathematical logic subjects, set theory is the study of infinity. This is the
main use of modern set theory it would seem.  It <b>can</b> be referred to as a
foundation of mathematics. But there are many foundations in the modern age of
mathematics. And to be fair, many mathematicians are not focussed enough on
methods and reliability of proofs. So concerns on methods and foundations are
left to the less gullible in the field.
<br>
<br>
The second is that a fairly common construct in set theory is different kinds
of numbers. But this second part may be more historical than realistic. This is
a valuable property for model theory, as model theory needs larger and larger
infinities of elements to toss around.
<br>
<br>
Another cool thing I found is set theory classically has some nice
computational elements to it. Unlike naive computability these elements are
almost always some high level infinity. It was proven that at least with ZF
sets, not doing so would end up with elements that work like regular numbers,
and that realistically any set theory would be excessive if it were not large.
"""
#}}}

griffiths.data = """
    <h3> Electrodynamics Griffiths 4th ed </h3>
    <a href="Griffiths/Preface.html"></a>
    <b>Preface</b>
    <br>
    <br>
    <b>Note to the reader</b>: The first chapter is meant to be a review of the language used to explain electrodynamics, not an explanation of foundations. Attention should be paid to how words are defined, but any metaphysical or logical arguments should be observed with a critical mind. Griffiths is unconnected with work outside of electromagnetism and particle physics, and consumed uncritically the teachings of his predecessors. No offense was meant to professionals of adjacent fields, probably.
    <br>
    <br>
    "The connection between light and electricity is now established . . . In every flame, in every luminous particle, we see an electrical process . . . Thus, the domain of electricity extends over the whole of nature. It even affects ourselves intimately: we perceive that we possess . . . an electrical organ—the eye."
    
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
In the book a tensor is n x m x o product of numbers. The design is to carry
physical information along calculus like transformations. Tensors in this
definition also work to make sure type information (units with some measure)
carries. They are tedious to write. (and they make you sound uncultured
math-wise). Instead these can be typed into python under the differential
geometry library in sympy.

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

intro_compilers.data = """
<b>Note</b>: Admittedly, my notes for this entire year are terrible. Everything was online. So I just rewatched parts of lectures if I forgot about something. And the course materials are copyrighted. So I am not allowed to share the main content of what was said or done. Sorry.
<br>
<br>
About time I got to take a compilers course. I have been wanting to get into
programming languages since sophomore year of undergrad. 
<br>
<br>
We made a C compiler to the Risc-V assembly language. The core insight I gained
from this: Many of the design features of C are so it will compile quickly on
the computers of the 1970s. But as a language it is annoying to build a
compiler for. It would be significantly easier to make compilers from lisp to
assembly as it would turn out.
<br>
<br>
Also, with modern compiler tools and maybe a month, anybody can make a good
chunk of the C language into machine level instructions. That is pretty much
what the Arduino people do. There are languages that it would simpler to do
this with (forth, lisp, some near-assembly lang) though. AT&T really left
behind a legacy with their language.
<br>
<br>
My enthusiasm for C programming kind of died in this class. C is old and
standard. Embedded systems are messy. 
"""

em.data = """
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
"""

# courses
courses.data = """
<p><b>Spring 2021</b></p>"""+(
inlink(ml)+
link(probability)+
link(stat_pattern))+"""

<p><b>Fall 2021</b></p>"""+(
inlink(ccl)+
link(algorithms)+
link(compilers)+

bar())+"""

<p><b>Summer 2021</b></p>"""+(
inlink(summer_of_logic)+

bar())+"""

<p><b>Spring 2021</b></p>"""+(
inlink(adv_compilers)+' (applied mathematical logic)'+
link(se))+"""

<p><b>Fall 2020</b></p>"""+(
inlink(set_theory)+
link(math_logic)+
link(intro_compilers))
#}}}

# lots of regex generation
def build_site() :
    build_page(home)

                                #... Byte me, python
    build_page(courses, courses/'/')
    #========================================================#
    build_page(ml, courses/ml/'/')
    build_page(probability, courses/probability/'/')
    build_page(stat_pattern, courses/stat_pattern/'/')
    build_page(ccl, courses/ccl/'/')
    build_page(ccl_book, courses/ccl/ccl_book/'/')
    build_page(comp_intract, courses/ccl/comp_intract/'/')
    build_page(comp_intract, courses/algorithms/comp_intract/'/')
    build_page(random_graphs, courses/ccl/random_graphs/'/')

    build_page(algorithms, courses/algorithms/'/')
    build_page(compilers, courses/compilers/'/')
    build_page(engineer_compiler, courses/compilers/compilers/'/')
    build_page(antlr_reference, courses/compilers/compilers/'/')
    build_page(summer_of_logic, courses/summer_of_logic/'/')
   
    build_page(pl, courses/summer_of_logic/pl/'/')
    build_page(tt, courses/summer_of_logic/tt/'/')
    build_page(topology, courses/summer_of_logic/topology/'/')

    build_page(adv_compilers, courses/adv_compilers/'/')
    build_page(se, courses/se/'/')

    build_page(set_theory, courses/set_theory/'/')
    build_page(math_logic, courses/math_logic/'/')
    build_page(intro_compilers, courses/intro_compilers/'/')

    build_page(em, courses/summer_of_logic/em/'/')
    build_page(griffiths, courses/summer_of_logic/em/griffiths/'/')


    build_page(blog,'blog/')
    #========================================================#
    for i in range(len(blogs)) :
        build_page(blogs[i],'blog/')

    build_page(research,'research/')

def main() :
    build_site()

main()

