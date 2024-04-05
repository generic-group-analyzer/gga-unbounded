all:
	jsx buttonView.jsx.js > buttonView.js
	jsx editorView.jsx.js > editorView.js
	tsc zoocrypt.ts
	tsc mainloop.ts

get-mathjax:
	curl -L https://github.com/mathjax/MathJax/archive/e1810fe2a90068646a918e4ee30b110f14591d1b.zip -o mathjax.zip
	unzip mathjax.zip
	mv MathJax-e1810fe2a90068646a918e4ee30b110f14591d1b imported/mathjax
