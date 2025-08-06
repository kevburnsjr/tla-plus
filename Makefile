hello:
	@java -cp tla2tools.jar tlc2.TLC -config hello_world/hello_world.cfg -workers auto -cleanup hello_world/hello_world.tla

diehard:
	@java -cp tla2tools.jar tlc2.TLC -config lamport/diehard/diehard.cfg -workers auto -cleanup lamport/diehard/diehard.tla

tcommit:
	@java -cp tla2tools.jar tlc2.TLC -config lamport/tcommit/tcommit.cfg -workers auto -cleanup lamport/tcommit/tcommit.tla

install:
	curl -LO https://github.com/informalsystems/apalache/releases/download/v0.17.5/apalache-v0.17.5.zip
	curl -LO https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/tla2tools.jar
	unzip apalache-v0.17.5.zip
	sudo apt install default-jdk
