-module(test).
-export([test/0]).

test() ->
    Fresh = vvclock:fresh(),
    vvclock:increment(1, Fresh),
    example_test().

% From Riak Core.
example_test() ->
    A = vvclock:fresh(),
    B = vvclock:fresh(),
    A1 = vvclock:increment(a, A),
    B1 = vvclock:increment(b, B),
    'True' = vvclock:descends(A1,A),
    'True' = vvclock:descends(B1,B),
    'False' = vvclock:descends(A1,B1),
    A2 = vvclock:increment(a, A1),
    C = vvclock:merge([A2, B1]),
    C1 = vvclock:increment(c, C),
    'True' = vvclock:descends(C1, A2),
    'True' = vvclock:descends(C1, B1),
    'False' = vvclock:descends(B1, C1),
    'False' = vvclock:descends(B1, A1),
    ok.
