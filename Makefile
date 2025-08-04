hello:
	@java -cp tla2tools.jar tlc2.TLC -config hello_world/hello_world.cfg -workers auto -cleanup hello_world/hello_world.tla

install:
	curl -LO https://github.com/informalsystems/apalache/releases/download/v0.17.5/apalache-v0.17.5.zip
	curl -LO https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/tla2tools.jar
	unzip apalache-v0.17.5.zip
	sudo apt install default-jdk
