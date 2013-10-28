# vvclocks

Verified vector clocks, with Coq!

## Configuring

First, add a rebar dependency:

```erlang
{vvclocks, ".*", {git, "git://github.com/cmeiklejohn/vvclocks", {branch, "master"}}}
```

Since rebar doesn't currently support the compilation of Core Erlang,
manually build the deps:

```erlang
cd deps/vvclocks
make
```

## Copyright

Copyright (C) 2013 Christopher Meiklejohn.
