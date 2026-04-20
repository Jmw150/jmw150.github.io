
default:
	python3 generate.py

clean :
	rm -f index.html
	rm -f about/about.html
	rm -f research/research.html
	rm -f courses/courses.html
	rm -f blog/blog.html
