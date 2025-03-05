all:
	git add --all
	git commit -m "I commit"
	git push -u origin main

go:
	make4ht web.tex "3,sec-filename,fn-in"

up:
	$(MAKE) -C /Users/mery/lectures/malg/webmovex ht	
	$(MAKE) -C /Users/mery/github/teaching all

