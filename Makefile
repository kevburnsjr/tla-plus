hello:
	@java -cp tla2tools.jar tlc2.TLC -config hello_world/hello_world.cfg -workers auto -cleanup hello_world/hello_world.tla

diehard:
	@java -cp tla2tools.jar tlc2.TLC -config lamport/diehard/diehard.cfg -workers auto -cleanup lamport/diehard/diehard.tla

tcommit:
	@java -cp tla2tools.jar tlc2.TLC -config lamport/tcommit/tcommit.cfg -workers auto -cleanup lamport/tcommit/tcommit.tla

twophase:
	@java -cp tla2tools.jar tlc2.TLC -config lamport/twophase/twophase.cfg -workers auto -cleanup lamport/twophase/twophase.tla

wire:
	@java -cp tla2tools.jar pcal.trans practical-tla-plus/wire.tla
	@java -cp tla2tools.jar tlc2.TLC -config practical-tla-plus/wire.cfg -workers auto -cleanup practical-tla-plus/wire.tla

trans:
	@echo "java -cp tla2tools.jar pcal.trans -h"

install:
	curl -LO https://github.com/informalsystems/apalache/releases/download/v0.17.5/apalache-v0.17.5.zip
	curl -LO https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/tla2tools.jar
	unzip apalache-v0.17.5.zip
	sudo apt install default-jdk
