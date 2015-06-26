all:
	jsx buttonView.jsx.js > buttonView.js
	jsx editorView.jsx.js > editorView.js
	tsc zoocrypt.ts
	tsc mainloop.ts

get-mathjax:
	curl -L https://github.com/mathjax/MathJax/archive/master.zip -o mathjax.zip
	unzip mathjax.zip
	mv MathJax-master imported/mathjax