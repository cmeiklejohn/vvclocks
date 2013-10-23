-module(test).
-export([test/0]).

test() ->
    Fresh = vvclock:fresh(),
    vvclock:increment(1, Fresh).
