.PHONY: rel deps test

all: deps compile

compile: deps
	@./rebar compile
	## Forced compilation of Core Erlang through erlc as it's not
	## supported by rebar.
	@erlc +debug_info -pa ebin -o ebin src/*.core src/*.erl

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

##
## Doc targets
##
docs:
	./rebar skip_deps=true doc
