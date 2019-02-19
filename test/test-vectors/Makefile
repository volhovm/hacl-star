.PRECIOUS: .gen-tests
.gen-tests:
	mkdir -p generated/json
	python3 gen_json.py
	mkdir -p generated/c
	python3 gen_c_tests.py
	touch .gen-tests
