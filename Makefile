all:
	git add --all
	git commit -m "I commit"
	git push -u origin main

go:
	make4ht web.tex "3,sec-filename,fn-in"
	cp web.html index.html

up:
	$(MAKE) -C /Users/mery/lectures/mosos/tutorials cp
	$(MAKE) -C /Users/mery/lectures/mosos/lectures-master slide
	$(MAKE) -C /Users/mery/webmery ht
	$(MAKE) -C /Users/mery/lectures/malg/webmovex ht
	$(MAKE) -C /Users/mery/lectures/mosos/webmosos ht
	$(MAKE) -C /Users/mery/lectures/mvsi/webmvsi ht
	$(MAKE) -C /Users/mery/lectures/mvsi/webaspd ht
#	$(MAKE) -C /Users/mery/github/teaching all

