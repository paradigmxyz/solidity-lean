// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {CatchDispatch} from "../src/CatchDispatch.sol";
import {
    Reverter36,
    ReverterErr,
    ReverterPanic,
    ReverterCustom
} from "../src/Reverters.sol";

/// Ground-truth (solc 0.8.35 / Foundry EVM) for try/catch dispatch by kind.
contract CatchDispatchForgeTest {
    /// A 36-byte Error-selector+zeros payload is NOT Error(string): catch(bytes).
    function testShortErrorRoutesToBytes() public {
        CatchDispatch c = new CatchDispatch();
        Reverter36 r = new Reverter36();
        (uint256 tag, , uint256 len) = c.route(address(r));
        require(tag == 4, "short-error -> bytes");
        require(len == 36, "raw len 36");
    }

    /// A well-formed Error("x") (>= 68 bytes) routes to catch Error(string).
    function testErrorRoutesToErrorClause() public {
        CatchDispatch c = new CatchDispatch();
        ReverterErr r = new ReverterErr();
        (uint256 tag, string memory reason, ) = c.route(address(r));
        require(tag == 2, "error -> Error clause");
        require(keccak256(bytes(reason)) == keccak256(bytes("x")), "reason x");
    }

    /// A Panic routes to catch Panic.
    function testPanicRoutesToPanicClause() public {
        CatchDispatch c = new CatchDispatch();
        ReverterPanic r = new ReverterPanic();
        (uint256 tag, , ) = c.route(address(r));
        require(tag == 3, "panic -> Panic clause");
    }

    /// A custom error routes to catch(bytes).
    function testCustomRoutesToBytes() public {
        CatchDispatch c = new CatchDispatch();
        ReverterCustom r = new ReverterCustom();
        (uint256 tag, , uint256 len) = c.route(address(r));
        require(tag == 4, "custom -> bytes");
        require(len == 36, "custom raw len 36");
    }

    /// Kind-based fall-through (A2): a Panic with no Panic clause -> catch(bytes).
    function testPanicFallsThroughToBytes() public {
        CatchDispatch c = new CatchDispatch();
        ReverterPanic r = new ReverterPanic();
        (uint256 tag, uint256 len) = c.routeNoPanic(address(r));
        require(tag == 4, "panic (no Panic clause) -> bytes");
        require(len == 36, "panic raw len 36");
    }
}
