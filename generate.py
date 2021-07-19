import time 
import os

# website data
# {{{

# nav_bar
# {{{
nav_bar = lambda css, home, research, courses, blog : """
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
     <a href="""+'"'+courses+'"'+"""> Course Notes </a></li>
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
     <a href="""+'"'+back['name']+'.html"'+""">Back: """+back['name']+"""</a>
    </div>
   </div>"""
    if nexts != None :
        bar += """
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+nexts['name']+'.html"'+""">Next: """+nexts['name']+"""</a></li>
    </div>
   </div>"""
    if up != None :
        bar += """
   <div id="nav_bar_li">
    <div id="nav_bar_li_a">
     <a href="""+'"'+up['name']+'.html"'+""">Up: """+up['name']+"""</a>
    </div>
   </div>
  </div>
 </div>
"""
    return bar
# }}}

# home
# {{{
home = """
<div id="content">

<div id="title">
  <font face="Albertus Medium">
    <h2><i>Jordan Winkler</i></h2>
    <h3>Logician, Computer Scientist </h3>
  </font>
</div>

<div id="upper_square">
  <br>
  <center>
    <img src="home/JordanWinkler.jpg" height="270" align="middle">
  </center>
</div>
 <div id="lower_square">
  <p>
    <a href="https://github.com/jmw150" target="_blank" >github</a>,
    <a href=" https://qoto.org/web/accounts/373087 " target="_blank" >mastodon</a>,
    <a href="https://twitter.com/JordanWinkler1" target="_blank" >twitter</a>,
    <a href="https://www.linkedin.com/in/jordan-winkler-65254283/" target="_blank" >linkedin</a>,
    <a href="JW_resume.pdf">CV</a>
 </div>
</div>
"""
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

# courses
# {{{
courses = """
<div id="content">
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
    <a href="summer_of_logic/index.html">
Summer of Logic
    </a>

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
</div>
"""
# }}}

# summer_of_logic
# {{{
summer_of_logic = """
<div id="content">
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
 </a>
        Topology
<br>
 <a href="
          em/Electromagnetism.html
         "
    target="_top">
        Eletromagnetic force
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
</div>
"""
# }}}

# em
#{{{
# topic head
em = {}
em['name'] = 'Electromagnetism'
em['prev'] = None
em['up'] = None
em['next'] = {}
griffiths = em['next']

# book head
griffiths['name'] = 'Griffiths'
griffiths['prev'] = None
griffiths['up'] = em
## Make chapters
for i in range(0,13) :
    griffiths[i] = {}
griffiths['next'] = griffiths[0]
## Make chapter names
griffiths[0]['name'] = 'Preface'
for i in range(1,13) :
    griffiths[i]['name'] = 'Chapter_'+str(i)

## create tree links
griffiths[0]['prev'] = None
for i in range(1,13) :
    griffiths[i]['prev'] = griffiths[i-1]
griffiths[12]['next'] = None
for i in range(1,13) :
    griffiths[12-i]['next'] = griffiths[12-(i-1)]
for i in range(0,13) :
    griffiths[i]['up'] = em

## create data
for i in range(0,13) :
    griffiths[i]['data'] = '<div id="content">'
griffiths[0]['data'] = """
<div id="content">
<b>Preface</b>
<br>
<br>
<b>Note to the reader</b>: The first chapter is meant to be a review of the language used to explain electrodynamics, not an explanation of foundations. Attention should be paid to how words are defined, but any metaphysical or logical arguments should be observed with a critical mind. Griffiths is unconnected with work outside of electromagnetism and particle physics, and consumed uncritically the teachings of his predecessors. No offense was meant to professionals of adjacent fields, probably.
</div>
"""
griffiths[1]['data'] = """
<div id="content">
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
</div>
"""
# {{{
em['data'] = """
<div id="content">

<br>
<b>Books</b>
<br><a href="Griffiths.html">Griffiths</a>
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
</div>
"""
# }}}
# {{{
griffiths['data'] = """
<div id="content">
<h3> Electrodynamics Griffiths 4th ed </h3>
<a href="Griffiths/Preface.html">Preface</a>"""
for i in range(1,13) :
    griffiths['data'] += ("<br><a href="
            +griffiths['name']+'/'
            +griffiths[i]['name']+".html>"
            +griffiths[i]['name']+"</a>\n")
griffiths['data'] += '</div>'
#}}}
#}}}

# blog
# {{{
blog = """
<div id="content">
 <b>Advice an old me needed, and a newer me might find foolish</b>
<br>
<br>
<br>
<a href="
why_are_proofs_hard.html
         "
        >
</a>
It is just topology all the way down
(Jul 13 2021)
<br>
<a href="
if_it_quacks_like_a_duck.html
         "
        >
If it quacks like a duck
</a>
(Jul 13 2021)
<br>
<a href="
why_are_proofs_hard.html
         "
        >
        Why are proofs hard?
</a>
(Jul 13 2021)
<br>
<a href="
science_of_cs.html
         "
        >
        The science in computer science
</a>
(Jul 12 2021)
<br>


<br>
</div>
"""
# }}}

# blogs 
# {{{
    #if_it_quacks_like_a_duck
# {{{
if_it_quacks_like_a_duck = """
<div id="content">
If it walks like a duck and talks like a duck.. It is a duck up to talking and walking homomorphisms.

<br>
<br>
But really, we never seem to find good bounds on when objects are the same.
Behavior is tracked, and that is an in-place method of making equivalence
classes. But, somebody found it disturbing that Star Trek teleporters are killing
and cloning people. Or classical example of the Ship of Theseus was kind of odd.

<br>
<br>
But there is not really anything to be said about objects that have infinite
attributes, in general. In the mind, without a finite representation of
attributes, there is no proof of uniqueness.

<br>
<br>
Can we really prove anything is all that we think of them, even numbers?
Something like 2000 has a different meaning between minds. The mind of
mathematician might pick it apart for all of the primes, groups with as many
elements, etc. To another, it was the year they got married. It is an integer, a string of letters, a real number.

<br>
<br>
<b>You think, therefore I am.</b>
</div>
"""
#}}}
    # it_is_just_topology_all_the_way_down
#{{{
it_is_just_topology_all_the_way_down = """

<div id="content">
It is just topology all the way down.

That was a pun. Real numbers on an interval (0,1] have numbers approaching 0 endlessly.
</div>
"""
#}}}
    # science_of_cs
#{{{
science_of_cs = """
<div id="content">
<h2> The Best of Computer Science</h2>
I think computer science, as it can be called a science, is a formal science,
predominantly. Many areas of CS such as operating system research and robotics,
can, and should, be considered computer engineering. Engineering is a noble
pursuit but the culture of engineering is about the creation of things.
Creation is the discovery of engineering.  

<br>
<br>
But what is left? The computer scientists that are also Logicians, Linguists,
or Cognitive Scientists. 

<br>
<br>
<b>Logicians and Linguists</b>
<br>
Ever since Wittgenstein, Logic as a practice has been explained as a language
game. I have taken this to be that the kind of language game that
fits a few criteria: consistency, precision, and predictability. Playing
the game well means trying to optimize these three criteria. If a system is not
consistent, then all things are possible. While it is possible to do this, to
lie, in common language.  It is also important to know when someone is telling
the truth. Our world in general is also filled with what-is and what-is-not,
and computing is very much the same. It is to a similar benefit that
computation is explored logically like this. For example, it is <i>not</i>
possible in general to tell if a program will halt, many algorithms <i>do</i>
have a bound of O(n). Knowing these things with precision means computers can
be complex without being full of bugs.  When I say predictability, I mean
Logic's ability to build a universe from a much smaller one. To be able to
understand this in computing is a form of discovery. A 32 bit computer has 2^32
possible programs. By some grammar, maybe, only a 1/10th of these programs fit
the grammar.  And then by some type theory, maybe, only 1/1000th of the
programs will do the correct task by specification. This was a deductive
process, a formally scientific process.

<br>
<br>
<b>Cognitive Scientists</b>
<br>
Contemporary Cognitive Scientists are concerned with (artificial) intelligence,
and how learning happens. Many outside of the discipline do not acknowledge AI
as a real concept. But this is reductionist. The mind-like behavior is there
already. And the path of what can be done with AI is already laid out by
similar disciplines: philosophy of the mind, psychology, epistemology, etc...
It is possible to explain much of AI using optimization and
linear algebra. But all the same, this would put AI into the first category. In
total cognition like things are also a space that is about discovery instead of
purely creation.
</div>
"""
#}}}
    # why_are_proofs_hard
#{{{
why_are_proofs_hard = """
<div id="content">
<h2> Why are Proofs Hard </h2>

Well, depending on the context, they are not really actually. But in undergraduate mathematics and sciences that rely on mathematics, it may seem so.
<br>
<br>
What can make proofs have a magical air to them in mathematics courses is the lack of clear explanation about what they are historically, and how we eventually arrived at teaching first order logic in introductory courses.

<br>
<br>
To start, a proof, historically, is an argument that is meant to convince another person of something. If the other person is incredibly gullible, a proof can be done with the same effort of a making a charismatic statement. Bad evidence of a possible truth is completely possible to be given. Proofs are not constructing the eternal, or are magic.
<br>
<br>
Proofs are all about the recipient. Providing proof of something in math/logic/philosophy is intended to be more productive. ('cause magic genius genes, but really) The recipient in this case is supposed to be trained in a few ways: in more exact language, and with the cultural knowledge of what reasoning leads to poor results. With this community reading what is being proven, there is a higher hope for the proof of a fact being good.
<br>
<br>
But it is important to not consider this style of language and reason a prescription. It is a convergent form. Misinterpretation happens in mathematics if the object of study is nuanced enough. The reality of this kept mathematics from going beyond euclidean and arithmetical topics for centuries. In the 1850s some thinkers became pretty creative (got lucky, stopped being stupid for 10 minutes). Logical form was being given algebraic structure. An idea of a domain of discourse was being used to allow logical sentences to be sound based on content instead of just form. 
<br>
<br>
From this new precision, intellectuals of the time got drunk on the new power of formalization. But what was also invited was complexity. Understanding and taming complexity is a feat that took half a century of working with digital computers to succeed at. So this is why first order logic is taught in an introduction to proofs course, and then promptly disregarded for the rest of many mathematicians careers. New results are exciting, oddly more so than reliable results. This is due to correctness by consensus.
<br>
<br>
This newfound precision also pointed out problems with past results. Arithmetical statements, as stated in the Peano formalization, are recursive. Unbound recursion is the cause of many logical paradoxes. So, remember the problem of prescription of language I mentioned earlier? Due to treating mathematics as mystical, eternal, and all connected, the culturally distinct idea of logical precision is blamed, instead of poor reasoning.
<br>
<br>
Formal proofs are not automatically correct. They are proofs taken from a list of possible inferences, instead of a more vague collective knowledge of good reasoning versus bad. And the language is naturally mechanical, so it is easier to grasp through use in computing. Many important things can be done in this formal, more computational, setting.
<br>
<br>
But, the recipient is what matters for a proof to work. Proofs are sophistry. Proofs are communal rituals.
<br>
<br>
It is your life. It is also up to you what you consider proven.
</div>
"""
#}}}

# }}}

# research
# {{{
research = """
<div id="content">
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
A discipline that is similar to the set of tools <a href="http://www.classicallibrary.org/descartes/meditations/">Descartes</a> would have used. Models sit on top of symbolic logic, and bear many similarities to algebraic geometry. They are the instances of programs, and the living breathing citizens of logical universes. Useful in 
    <a href="
                https://www.amazon.com/Philosophy-Model-Theory-Tim-Button/dp/0198790406/
                ">
                Philosophy</a>,  
        and 
        <a href="
           https://en.wikipedia.org/wiki/Finite_model_theory
                ">
                Computer Science</a>.
</li>
<!--
<br>
<li><b>Algebraic Topology</b>: Generally softer geometric equalities and structures. Topologies can be used to do things normally done with a logic, such as defining spaces for mathematical analysis to work.

</li>
<br>
<li><b>Algebraic Geometry</b>: 
Multivariate polynomials, and structures defined as solutions to a larger
series of equations. The magic (for me at least) of having a solution to an
equation is a popular theme in algebraic geometry. Looking into 
<a
href="
      https://www.math.uwaterloo.ca/~snburris/htdocs/MAL.pdf
">The Mathematical Analysis of Logic</a> you will find that the original Boolean Algebra, the
first logical species of mathematical structures, was defined more as systems
of equations, than the common operator based structure found today in
undergraduate texts.  

</li>
-->

<!--
<br>
<li><b>Constructive Mathematics</b>: 
Mathematics is grand, powerful, and even beautiful. But, I am not gullible, or desperate for just any mathematics teaching job. So I can take my time, be more constructive, and more intuitive about mathematical discoveries. Constructive methods are more dependable, simple to verify, and translate between logics, or into programs. 

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
 </a> (May 2019)
    </li>
</ul>

</td></tr></tbody></table> </p> </p> </center> <hr>

<h2>Projects</h2>

See <a href="https://github.com/jmw150" target="_blank" >github</a>.
</div>
"""
#}}}

#}}}

# Paths
# {{{
css = 'bluestyle.css'
home_path = 'index.html'
research_path = 'research/index.html'
course_path = 'courses/index.html'
blog_path = 'blog/index.html'
# }}}

def write_file(file, content):
    f = open(file, "w")
    f.write(content)
    f.close()

def build_page(level,file,content) :
    ab = '../'*level
    write_file(file,
            (nav_bar(
                ab+css,
                ab+home_path,
                ab+research_path,
                ab+course_path,
                ab+blog_path)
                +content+update))

# wiki book style
def build_book(level:int, chapter:int, file_base:str, content:dict) :

    # exit base case
    if content == None :
        return 

    if content['data'] == None :
        content['data'] = ''
    # recursion case
    ab = '../'*level
    write_file(file_base+'/'+content['name']+'.html',
            (note_bar(
                ab+css,
                ab+home_path,
                content['name'],
                content['prev'],
                content['next'],
                content['up']
        )+content['data']+update))

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
    build_page(0,'index.html',home)
    build_page(1,'courses/index.html',courses)
    build_page(2,'courses/summer_of_logic/index.html',summer_of_logic)
   
    build_book(3,0,'courses/summer_of_logic/em',em)

    build_page(1,'blog/index.html',blog)
    build_page(1,'blog/if_it_quacks_like_a_duck.html',if_it_quacks_like_a_duck)
    build_page(1,'blog/it_is_just_topology_all_the_way_down.html',
            it_is_just_topology_all_the_way_down)
    build_page(1,'blog/science_of_cs.html',science_of_cs)
    build_page(1,'blog/why_are_proofs_hard.html',why_are_proofs_hard)
    build_page(1,'research/index.html',research)

def main() :
    build_site()

main()

