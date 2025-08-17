hello:
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config hello_world/hello_world.cfg -workers auto -cleanup hello_world/hello_world.tla

diehard:
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config lamport/diehard/diehard.cfg -workers auto -cleanup lamport/diehard/diehard.tla

tcommit:
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config lamport/tcommit/tcommit.cfg -workers auto -cleanup lamport/tcommit/tcommit.tla

twophase:
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config lamport/twophase/twophase.cfg -workers auto -cleanup lamport/twophase/twophase.tla

wire:
	@java -XX:+UseParallelGC -cp tla2tools.jar pcal.trans practical-tla-plus/wire.tla
	@bin/tlafmt --in-place practical-tla-plus/wire.tla
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config practical-tla-plus/wire.cfg -workers auto -cleanup practical-tla-plus/wire.tla

recycler:
	@java -XX:+UseParallelGC -cp tla2tools.jar pcal.trans practical-tla-plus/recycler.tla
	@bin/tlafmt --in-place practical-tla-plus/recycler.tla
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config practical-tla-plus/recycler.cfg -workers auto -cleanup practical-tla-plus/recycler.tla

telephone:
	@java -XX:+UseParallelGC -cp tla2tools.jar pcal.trans practical-tla-plus/telephone.tla
	@bin/tlafmt --in-place practical-tla-plus/telephone.tla
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config practical-tla-plus/telephone.cfg -workers auto -cleanup practical-tla-plus/telephone.tla

knapsack:
	@java -XX:+UseParallelGC -cp tla2tools.jar pcal.trans practical-tla-plus/knapsack.tla
	@bin/tlafmt --in-place practical-tla-plus/knapsack.tla
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config practical-tla-plus/knapsack.cfg -workers auto -cleanup practical-tla-plus/knapsack.tla

message_queue:
	@java -XX:+UseParallelGC -cp tla2tools.jar pcal.trans practical-tla-plus/message_queue.tla
	@bin/tlafmt --in-place practical-tla-plus/message_queue.tla
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config practical-tla-plus/message_queue.cfg -workers auto -cleanup practical-tla-plus/message_queue.tla

cache:
	@java -XX:+UseParallelGC -cp tla2tools.jar pcal.trans practical-tla-plus/cache.tla
	@bin/tlafmt --in-place practical-tla-plus/cache.tla
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config practical-tla-plus/cache.cfg -workers auto -cleanup practical-tla-plus/cache.tla

traffic:
	@java -XX:+UseParallelGC -cp tla2tools.jar pcal.trans practical-tla-plus/traffic.tla
	@bin/tlafmt --in-place practical-tla-plus/traffic.tla
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config practical-tla-plus/traffic.cfg -workers auto -cleanup practical-tla-plus/traffic.tla

dekker:
	@java -XX:+UseParallelGC -cp tla2tools.jar pcal.trans practical-tla-plus/dekker.tla
	@bin/tlafmt --in-place practical-tla-plus/dekker.tla
	@java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config practical-tla-plus/dekker.cfg -workers auto -cleanup practical-tla-plus/dekker.tla

trans:
	@echo "java -XX:+UseParallelGC -cp tla2tools.jar pcal.trans -h"

install:
	curl -LO https://github.com/informalsystems/apalache/releases/download/v0.17.5/apalache-v0.17.5.zip
	curl -LO https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/tla2tools.jar
	curl -LO https://github.com/domodwyer/tlafmt/releases/download/v0.4.1/tlafmt_v0.4.1_x86_64-unknown-linux-musl.tar.gz
	unzip apalache-v0.17.5.zip
	tar xvfz tlafmt_v0.4.1_x86_64-unknown-linux-musl.tar.gz
	mv release/tlafmt_v0.4.1_x86_64-unknown-linux-musl bin/tlafmt
	rm -rf release
	rm -rf tlafmt_v0.4.1_x86_64-unknown-linux-musl.tar.gz
	rm -rf apalache-v0.17.5.zip
	sudo apt install -y default-jdk
