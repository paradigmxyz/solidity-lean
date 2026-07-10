// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/CalldataLazyValue.sol";

// Real-EVM ground truth for the calldata-lazy-value divergence: a DIRTY value
// element of a calldata array/struct is validated lazily (on access), never at
// the dispatch boundary. Every call below hand-builds calldata carrying a dirty
// element (a bool word == 2, an address word with dirty high bits) that
// `abi.encode` would otherwise clean.
contract CalldataLazyValueForgeTest {
    CalldataLazyValueHarnessTarget private target;

    function setUp() public {
        target = new CalldataLazyValueHarnessTarget();
    }

    bytes32 constant DIRTY_BOOL = bytes32(uint256(2));
    // address word with dirty high bits (all-ones): not maskable to 160 bits.
    bytes32 constant DIRTY_ADDR =
        bytes32(uint256(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff));

    // --- bool[]: dirty element NOT accessed -> success, returns length ------
    function testBoolLenDirtyNotAccessedSucceeds() public {
        bytes memory cd = abi.encodePacked(
            bytes4(keccak256("boolLen(bool[])")),
            bytes32(uint256(0x20)), // offset to array
            bytes32(uint256(1)),    // length 1
            DIRTY_BOOL              // b[0] = 2 (dirty)
        );
        (bool ok, bytes memory ret) = address(target).call(cd);
        require(ok, "dirty bool not accessed must succeed");
        require(
            ret.length == 32 && abi.decode(ret, (uint256)) == 1,
            "boolLen must return 1"
        );
    }

    // --- bool[]: dirty element ACCESSED -> empty revert --------------------
    function testBoolAtDirtyAccessedReverts() public {
        bytes memory cd = abi.encodePacked(
            bytes4(keccak256("boolAt(bool[],uint256)")),
            bytes32(uint256(0x40)), // offset to array (past 2 head words)
            bytes32(uint256(0)),    // i = 0
            bytes32(uint256(1)),    // length 1
            DIRTY_BOOL              // b[0] = 2 (dirty)
        );
        (bool ok, bytes memory ret) = address(target).call(cd);
        require(!ok, "accessing dirty bool must revert");
        require(ret.length == 0, "dirty bool access reverts empty");
    }

    // --- address[]: dirty high bits NOT accessed -> success ----------------
    function testAddrLenDirtyNotAccessedSucceeds() public {
        bytes memory cd = abi.encodePacked(
            bytes4(keccak256("addrLen(address[])")),
            bytes32(uint256(0x20)),
            bytes32(uint256(1)),
            DIRTY_ADDR
        );
        (bool ok, bytes memory ret) = address(target).call(cd);
        require(ok, "dirty address not accessed must succeed");
        require(
            ret.length == 32 && abi.decode(ret, (uint256)) == 1,
            "addrLen must return 1"
        );
    }

    // --- address[]: dirty high bits ACCESSED -> empty revert ---------------
    function testAddrAtDirtyAccessedReverts() public {
        bytes memory cd = abi.encodePacked(
            bytes4(keccak256("addrAt(address[],uint256)")),
            bytes32(uint256(0x40)),
            bytes32(uint256(0)),
            bytes32(uint256(1)),
            DIRTY_ADDR
        );
        (bool ok, bytes memory ret) = address(target).call(cd);
        require(!ok, "accessing dirty address must revert");
        require(ret.length == 0, "dirty address access reverts empty");
    }

    // --- static struct: dirty member NOT accessed -> success --------------
    function testStructValDirtyMemberNotAccessedSucceeds() public {
        bytes memory cd = abi.encodePacked(
            bytes4(keccak256("structVal((bool,uint256))")),
            DIRTY_BOOL,             // s.flag = 2 (dirty), inline
            bytes32(uint256(42))    // s.val = 42 (clean sibling)
        );
        (bool ok, bytes memory ret) = address(target).call(cd);
        require(ok, "dirty struct member not accessed must succeed");
        require(
            ret.length == 32 && abi.decode(ret, (uint256)) == 42,
            "structVal must return 42"
        );
    }

    // --- static struct: dirty member ACCESSED -> empty revert -------------
    function testStructFlagDirtyMemberAccessedReverts() public {
        bytes memory cd = abi.encodePacked(
            bytes4(keccak256("structFlag((bool,uint256))")),
            DIRTY_BOOL,
            bytes32(uint256(42))
        );
        (bool ok, bytes memory ret) = address(target).call(cd);
        require(!ok, "accessing dirty struct member must revert");
        require(ret.length == 0, "dirty struct member access reverts empty");
    }
}
