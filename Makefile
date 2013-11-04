.PHONY: rel deps test

all: deps compile

compile: deps
	@./rebar compile

app:
	@./rebar compile skip_deps=true

deps:
	@./rebar get-deps

clean:
	@./rebar clean

distclean: clean
	@./rebar delete-deps

test: all
	@./rebar skip_deps=true eunit

itest: all
	erl -pa ebin -noshell -s test test -s init stop

##
## Doc targets
##
docs:
	./rebar skip_deps=true doc
