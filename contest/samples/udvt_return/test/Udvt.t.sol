// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Udvt, U, W} from "../src/Udvt.sol";

// Asserts the REAL solc+EVM behavior of f(U.wrap(-7), V.wrap(-3)).
contract UdvtTest {
    function test_signed_udvt_returns() public {
        Udvt t = new Udvt();
        (U a, Udvt.V[2] memory vs, Udvt.S memory s, Udvt.E e, W[] memory ws) =
            t.f(U.wrap(-7), Udvt.V.wrap(-3));
        require(U.unwrap(a) == -7, "a");
        require(Udvt.V.unwrap(vs[0]) == -3 && Udvt.V.unwrap(vs[1]) == -2, "vs");
        require(U.unwrap(s.a) == -14 && Udvt.V.unwrap(s.b) == -3, "s");
        require(W.unwrap(s.c) == 65535, "s.c");
        require(e == Udvt.E.C, "e");
        require(ws.length == 2 && W.unwrap(ws[1]) == 2, "ws");
    }
}
