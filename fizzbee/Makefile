
install:
	curl -LO https://github.com/fizzbee-io/fizzbee/releases/download/v0.1.2/fizzbee-v0.1.2-linux_x86.tar.gz
	tar xvfz fizzbee-v0.1.2-linux_x86.tar.gz
	mkdir bin
	cp -r fizzbee-v0.1.2-linux_x86/* bin
	rm -rf fizzbee-v0.1.2-linux_x86*

quickstart:
	@./bin/fizz quickstart/spec.fizz

.PHONY: quickstart
