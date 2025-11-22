run:
	@java -XX:+UseParallelGC -cp ../../tla2tools.jar pcal.trans spec.tla
	@../../bin/tlafmt --in-place spec.tla
	@java -XX:+UseParallelGC -cp ../../tla2tools.jar tlc2.TLC -config spec.cfg -workers auto -cleanup spec.tla
