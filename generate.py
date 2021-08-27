# A python script to generate websites
# Jordan Winkler

# NOTE: could set up data to be a list: [if not str, insert var]
## but it would probably be better to hash address variables

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
css = Tag('greywhite.css')
data = Tag('data')
#}}}

class Page (Tag):
    #{{{
    "A website page"
    def __init__(self, name, data=' ', nickname= '', nav=[], preprocess=True) :
        self.name = name
        if nickname == '':
            self.nickname = name
        else:
            self.nickname = nickname
        self.data = data
        self.preprocess = preprocess
        self.subdata = [] # for some reason this assigned recursively

        # default stuff
        home = Tag('index', nickname='Home')
        research = Tag('research/research',nickname='Research')
        courses = Tag('courses/courses', nickname='Courses')
        blog = Tag('blog/blog', nickname='Blog')
        about = Tag('about/about', nickname='About')

        # extra possible metadata
        if nav == [] : 
            self.nav = [
                    home,
                    research,
                    courses,
                    blog,
                    ]
        else :
            self.nav = nav

    # this is odd design, Python
    def __add__(self, y) :
        if type(y) == Page :
            return Page(self.name, str(self.data) + str(y.data), 
                    self.nickname, self.nav, self.preprocess)
        else :
            return Page(self.name, str(self.data) + str(y), 
                    self.nickname, self.nav, self.preprocess)

    def __radd__(self,y) :
        if type(y) == Page :
            return Page(self.name, str(self.data) + str(y.data), 
                    self.nickname, self.nav, self.preprocess)
        else :
            return Page(self.name, str(self.data) + str(y), 
                    self.nickname, self.nav, self.preprocess)

    # looks like a path variable
    def __truediv__(self, y='/') : # doesn't matter, a/ is still a syntax error
        if type(y) == Page :
            return Page(str(self.name) + '/' + str(y.name), 
                self.data, self.nickname, self.nav, self.preprocess)
        else :
            return Page(str(self.name) + str(y), 
                self.data, self.nickname, self.nav, self.preprocess)


    def __rtruediv__(self, y) :
        if type(y) == Page :
            return Page(str(y.name) + '/' + str(self.name), 
                self.data, self.nickname, self.nav, self.preprocess)
        else :
            return Page(str(y) + str(self.name), 
                self.data, self.nickname, self.nav, self.preprocess)
    
    # get data, also process data
    def dat(self, size=2) : # size might be another property to add
        
        if self.preprocess == True :
            # double enter -> html 
            data = self.data.replace('\n\n','<br><br>\n') 
        
            s = str(size)
    
            # add title
            self.data = '\n<h'+s+'>'+self.nickname.replace('_',' ').title()+'</h'+s+'>\n'
            self.data += data

            # recursive link
            for node in self.subdata :
                self.data += inlink(node)
                self.data += '<br>'
    
            self.preprocess = False
            # TODO: evaluate links in data

        return self.data

    def sub(self, page) :
        self.subdata.append(page)
#}}}

# html macros
link = lambda page :   '<br><a href='+page.name+'/'+page.name+'.html>'+page.nickname+'</a>'
inlink = lambda page :     '<a href='+page.name+'/'+page.name+'.html>'+page.nickname+'</a>'
exlink = lambda page : '<br><a target="_blank" href='+page.name+'>'+page.nickname+'</a>'
link_here = lambda page : '<br><a href='+page.name+'.html>'+page.nickname+'</a>'
link_here_cap = lambda page : '<br><a href='+page.name+'.html>'+page.nickname.replace('_',' ').title()+'</a>'
bar = lambda : '</td></tr></tbody></table></p></p></center><hr>'

def get_file(filename) :
    File = ""
    with open(filename) as f:
        for l in f.readlines() :
            File += l

    return File

def get_blogs(path:str) -> List[Page]:
    "get a array of blog pages"

    # get blog list at location
    bloglist = os.popen('ls -t '+path).read().split('\n')[:-1]

    # get those times
    timelist = os.popen('ls -lt --time-style=long-iso '+path).read().split('\n')[:-1]
    timelist = timelist[1:]
    a = timelist[:]
    timelist = []
    for i in a:
        timelist.append(i.replace('  ',' ').split(' '))
    a = timelist[:]
    timelist = []
    for i in a:
        timelist.append(i[5])

    blogs = []
    # add title to work, and clump together
    for i in bloglist :
        file = get_file(path+'/'+i)
        file = str(Page(i,file).dat())
        blogs.append(Page(i,file,preprocess=False))
    
    return blogs, timelist 

def write_file(file, content):
    f = open(file+'.html', "w")
    f.write(content)
    f.close()

def build_tree(content,path='') :

    # base case
    build_page(content,path)

    # breadth first recursive case
    if content.subdata != [] :
        for sub_content in content.subdata :
            build_tree(sub_content, path.name+sub_content.name+'/')

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

# main list
css = Page('greywhite.css', preprocess=False)
data = Page('data', preprocess=False)
home = Page('index', nickname='Home', preprocess=False)
courses = Page('courses', nickname='Courses', preprocess=False)
research = Page('research', nickname='Research', preprocess=False)
blog = Page('blog', nickname='Blog', preprocess=False)
about = Page('about', nickname='About', preprocess=False)

# books
griffiths = Page('griffiths',nickname='Griffiths')
set_theory_book = Page('st_book',nickname='Classic Set Theory')
math_logic_book = Page('math_logic_book',nickname='Introduction to Mathematical Logic')
software_foundations = Page('software_foundations', nickname='Software Foundations')
practical_software_foundations = Page('software_foundations', nickname='Software Foundations')

# spring 2022
ml = Page('machine_learning',nickname='ECE 595 Machine Learning')
probability = Page('probability',nickname="ECE 600 Random Variables and Signals")
lumped_system_theory = Page('lumped_system_theory', nickname='ECE 602 Lumped System Theory')

# fall 2021
deep_learning = Page('dl', nickname='ECE 595 Deep Learning')
ccl = Page('ccl', nickname='ECE 664 Computability, Complexity, and Languages')
algorithms = Page('algorithms', nickname='ECE 608 Computational Models and Methods')
compilers = Page('compilers', nickname='ECE 595 Compilers: optimization, code generation')
fall_research = Page('research', nickname='Research')

ccl_n = Page('class', nickname='Course Notes')
alg_n = Page('class', nickname='Course Notes')
compilers_n = Page('class', nickname='Course Notes')

# summer 2021
summer_of_logic = Page('summer_of_logic',nickname='Summer of Logic',preprocess=False)
pl = Page('programming_languages',nickname='Programming Language Theory')
tt = Page('type_theory',nickname='Type Theory')
topology = Page('topology',nickname='Topology')
em = Page('Electromagnetism',nickname='Electromagnetic Force')

# spring 2021
adv_compilers = Page('adv_compilers',nickname='ECE 663 Advanced compilers')
se = Page('software_engineering',nickname='ECE 595 Advanced Software Engineering')

# fall 2020
set_theory = Page('set_theory',nickname='MA  598 Set Theory')
math_logic = Page('mathemetical_logic',nickname='MA  585 Mathematical Logic')
intro_compilers = Page('intro_compilers',nickname='ECE 595 Intro to Compilers')


ccl_book = Page('ccl_book', nickname='The Book')
comp_intract = Page('comp_intract', nickname='Computers and Intractability')
random_graphs = Page('random_graphs', nickname='Random Graphs')

algorithms_book = Page('alg_book', nickname='Introduction to Algorithms')

engineering_a_compiler = Page('engineering_a_compiler', nickname='Engineering a Compiler')
antlr_reference = Page('antlr', nickname='ANTLR Reference Book')
#}}}

# connections
#{{{
ccl.sub(ccl_book)
ccl.sub(comp_intract)
ccl.sub(random_graphs)
ccl.sub(ccl_n)

algorithms.sub(alg_n)
#}}}

# web data
#{{{
home.data = """
    <h2>Welcome to my website</h2>
"""

# navigation bar (nav_bar)
#{{{
def nav_bar (css, args) :
    bar = """
<!DOCTYPE html PUBLIC "-//w3c//dtd html 5.0 transitional//en">
<html>
 <head>
   <meta name="viewport" content="width=device-width">
   <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
   <title>Logic Sea</title>
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
blogs, timelist = get_blogs(blogs_source) # started (Jul 12 2021)
blog.data = """ 
<!-- 
    <b>I drink and I know things</b> 
    <b>He just keeps talking</b>
-->
<b>What's new?</b>
<br>
<br>
"""
for i in range(len(blogs)) :
    blog.data += link_here_cap(blogs[i]) + '<br> (updated: '+timelist[i]+')<br>'
#}}}
# research
#{{{
research = Page('research', eval(get_file('../../research_goals')), preprocess=False)
#}}}
# home (index)
## mildly better info-sec, name is not on main tree

# about
#{{{
about.data = """
<div id="title">
 <font face="Albertus Medium">
  <h2><i>Jordan Winkler</i></h2>
  <h3>Logician, Computer Scientist </h3>
 </font>
</div>

<div id="upper_square">
 <br>
 <center>
  <img src="../data/JordanWinkler.jpg" height="270" align="middle">
 </center>
</div>
<div id="lower_square">
 <p>
  <a href="https://github.com/jmw150" target="_blank" >github</a>,
  <a href=" https://qoto.org/web/accounts/373087 " target="_blank" >mastodon</a>,
<!--  <a href="https://twitter.com/JordanWinkler1" target="_blank" >twitter</a>, -->
  <a href="https://www.linkedin.com/in/jordan-winkler-65254283/" target="_blank" >linkedin</a>,
  <a href="data/JW_resume.pdf">CV</a>
</div>
"""
#}}}

# spring 2022
#{{{
ml.data = """
<b>Motivation:</b> Its one of the cooler parts of AI

<b>personal note:</b> As of writing this, I am a machine learning scientist. (yay) 
I hope I get Chan for this topic though. His course covers convex optimization
and a bunch of more mathematical aspects of machine learning. Having a healthy
career in a topic means building a good foundation.  

https://engineering.purdue.edu/ChanGroup/ECE595/
"""

lumped_system_theory.data = """
<b>Motivation:</b> System and control theory are used in robotics and other areas that require considering feedback loops. This is the mostly linear introductory course to these fields. This is also a set of methods that can be used to help make machine learning programs scalable.
"""

probability.data = """
<b>Motivation:</b> Signals are an interesting aspect of system engineering. Combine it with electrodynamics, and you have physical computation on almost anything.
"""
#}}}

# fall 2021
#{{{
ccl.data = eval(get_file('../../fall2021/ccl/note_intro')) 
compilers.data = eval(get_file('../../fall2021/compilers/note_intro')) 
engineering_a_compiler.data =eval(get_file('../../fall2021/compilers/engineering_a_compiler_notes')) 
algorithms.data = eval(get_file('../../fall2021/algorithms/intro_note'))
fall_research.data = eval(get_file('../../fall2021/research/intro_note'))
#}}}

# summer 2021
#{{{
summer_of_logic.data = eval(get_file('../../summer2021/summer_of_logic_intro'))

tt.data = eval(get_file('../../summer2021/type_theory_notes'))
pl.data = eval(get_file('../../summer2021/programming_languages_notes'))
topology.data = eval(get_file('../../summer2021/topology_notes'))
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

    I learned that software engineering is a subset of system engineering.
    System engineering is actually novel. Software engineering before this
    class seemed to be all about middle management of the actual programmers,
    and using mathematical techniques to manage projects better.

    This was also a good course in the sense that we read current software
    engineering research articles and I was able to finish some actual
    scientific research in it.

        "https://engineering.purdue.edu/ECE/Academics/Online/Courses/advanced-software-engineering"
    """

math_logic.data = """
<b>Note</b>: Admittedly, my notes for this entire year are terrible. Everything was online. So I just rewatched parts of lectures if I forgot about something. And the course materials are copyrighted. So I am not allowed to share the main content of what was said or done. Sorry.

I have already taken a philosophical logic (pure-blooded logic) course. So I
may leave out some details, as those are trivial to me.

The online offering of Mathematical Logic is why I decided to go to main campus
Purdue for the pandemic of 2020. Purdue often ranking in the single digits in
the US, for engineering disciplines, was cool. But I am only a practical person
to pay the bills.

We covered propositional logic for about a week, and the dived into predicate
logic based model theory for 70% of the semester, finally finishing up with
formal number theory and the classic Gödel theorems.

Model are an amazing way to talk about mathematics. It is heavy. But this kind
of weight of tools is a good investment when working with high infinity objects
with concreteness. In the class models were treated as sacred and real thing.
But it is really just a design. A model can be pulled out of a logic. Stuff
like separation algebra exists as a model for separation logic.

Models are a lot like universal algebra and
algebraic geometry. The professors research subject is even in O-minimality,
which, from my understanding have a lot of connections to some types of
algebraic geometry.  

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

Mathematical logic is a giant field. We did not have time for Recursion Theory
or Set Theory. Luckily I took a separate course on at least <a
href="../set_theory/set_theory.html">Set Theory</a> this semester.  
"""

set_theory.data = """
<b>Note</b>: Admittedly, my notes for this entire year are terrible. Everything was online. So I just rewatched parts of lectures if I forgot about something. And the course materials are copyrighted. So I am not allowed to share the main content of what was said or done. Sorry.

This class started from the foundations of set theory as they were talked about historically. 

The main insight I gathered from set theory is that of the classical
mathematical logic subjects, set theory is the study of infinity. This is the
main use of modern set theory it would seem.  It <b>can</b> be referred to as a
foundation of mathematics. But there are many foundations in the modern age of
mathematics. And to be fair, many mathematicians are not focussed enough on
methods and reliability of proofs. So concerns on methods and foundations are
left to the less gullible in the field.

The second is that a fairly common construct in set theory is different kinds
of numbers. But this second part may be more historical than realistic. This is
a valuable property for model theory, as model theory needs larger and larger
infinities of elements to toss around.

Another cool thing I found is set theory classically has some nice
computational elements to it. Unlike naive computability these elements are
almost always some high level infinity. It was proven that at least with ZF
sets, not doing so would end up with elements that work like regular numbers,
and that realistically any set theory would be excessive if it were not large.
"""
#}}}

# other 
#{{{
griffiths.data = eval(get_file('../../summer2021/griffiths_notes'))

intro_compilers.data = """
<b>Note</b>: Admittedly, my notes for this entire year are terrible. Everything was online. So I just rewatched parts of lectures if I forgot about something. And the course materials are copyrighted. So I am not allowed to share the main content of what was said or done. Sorry.

About time I got to take a compilers course. I have been wanting to get into
programming languages since sophomore year of undergrad. 

We made a C compiler to the Risc-V assembly language. The core insight I gained
from this: Many of the design features of C are so it will compile quickly on
the computers of the 1970s. But as a language it is annoying to build a
compiler for. It would be significantly easier to make compilers from lisp to
assembly as it would turn out.

Also, with modern compiler tools and maybe a month, anybody can make a good
chunk of the C language into machine level instructions. That is pretty much
what the Arduino people do. There are languages that it would simpler to do
this with (forth, lisp, some near-assembly lang) though. AT&T really left
behind a legacy with their language.

My enthusiasm for C programming kind of died in this class. C is old and
standard. Embedded systems are messy. 
"""

em.data = """
<br>
<b>Books</b>"""+(
link(griffiths))+"""
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
#}}}

# courses
courses.data = """
<p><b>Spring 2021</b></p>"""+(
inlink(ml)+
link(probability)+
link(lumped_system_theory))+"""

<p><b>Fall 2021</b></p>"""+(
inlink(deep_learning)+
link(compilers)+
link(algorithms)+
link(ccl)+
link(fall_research)+

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
    # when the navigation bar needs another entry
    #home.nav.append(Page(str(about/about), nickname='About'))
    pl.nav.append(Page(str(courses/summer_of_logic/summer_of_logic), nickname='SoL'))
    tt.nav.append(Page(str(courses/summer_of_logic/summer_of_logic), nickname='SoL'))
    topology.nav.append(Page(str(courses/summer_of_logic/summer_of_logic), nickname='SoL'))
    em.nav.append(Page(str(courses/summer_of_logic/summer_of_logic), nickname='SoL'))
    
    ccl_book.nav.append(Page(str(courses/ccl/ccl),nickname='CCL'))
    random_graphs.nav.append(Page(str(courses/ccl/ccl),nickname='CCL'))
    comp_intract.nav.append(Page(str(courses/ccl/ccl),nickname='CCL'))

    build_tree(home)
    build_tree(about, about/'/')

    # books
    build_tree(comp_intract, courses/algorithms/comp_intract/'/')

    # skeleton 
    build_tree(courses,         courses/'/')
    #course_stuff========================================================#
    build_tree(ml,              courses/ml/'/')
    build_tree(probability,     courses/probability/'/')
    build_tree(lumped_system_theory,    courses/lumped_system_theory/'/')
    build_tree(ccl,             courses/ccl/'/')

    build_tree(algorithms,      courses/algorithms/'/')
    build_tree(deep_learning,   courses/deep_learning/'/')
    build_tree(compilers,       courses/compilers/'/')
    build_tree(ccl,             courses/ccl/'/')
    build_tree(fall_research,             courses/fall_research/'/')

    build_tree(engineering_a_compiler,    courses/compilers/engineering_a_compiler/'/')
    build_tree(antlr_reference, courses/compilers/antlr_reference/'/')
    build_tree(summer_of_logic, courses/summer_of_logic/'/')
   
    build_tree(pl,              courses/summer_of_logic/pl/'/')
    build_tree(tt,              courses/summer_of_logic/tt/'/')
    build_tree(topology,        courses/summer_of_logic/topology/'/')

    build_tree(adv_compilers,   courses/adv_compilers/'/')
    build_tree(se,              courses/se/'/')

    build_tree(set_theory,      courses/set_theory/'/')
    build_tree(math_logic,      courses/math_logic/'/')
    build_tree(intro_compilers, courses/intro_compilers/'/')

    build_tree(em,              courses/summer_of_logic/em/'/')
    build_tree(griffiths,       courses/summer_of_logic/em/griffiths/'/')

    build_page(blog,'blog/')
    #========================================================#
    for i in range(len(blogs)) :
        build_page(blogs[i],'blog/')

    build_page(research,'research/')

def main() :
    build_site()

main()

