all: lott lott-examples

.PHONY: lott
lott:
	lake build Lott

.PHONY: lott-examples
lott-examples:
	lake build -R LottExamples LottExamples.Tex

.PHONY: lott-examples-tex
lott-examples-noterm:
	lake build -R LottExamples.Tex -K noterm=1

.PHONY: lott-examples
lott-examples-notex:
	lake build -R LottExamples -K notex=1
