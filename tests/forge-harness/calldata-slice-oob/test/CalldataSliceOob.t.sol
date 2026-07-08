// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/CalldataSliceOob.sol";

contract CalldataSliceOobForgeTest {
    CalldataSliceOobHarnessTarget private target;

    function setUp() public {
        target = new CalldataSliceOobHarnessTarget();
    }

    // OOB slice `j > length`: empty revert (success == false, returndata length 0).
    function testSliceEndBeyondLengthEmptyRevert() public {
        bytes memory input = hex"0a141e"; // 3 bytes
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature(
                "slice(bytes,uint256,uint256)", input, uint256(1), uint256(100)
            )
        );
        require(!ok, "slice OOB should revert");
        require(ret.length == 0, "slice OOB returndata must be empty");
    }

    // OOB slice `i > j`: empty revert.
    function testSliceStartAfterEndEmptyRevert() public {
        bytes memory input = hex"0a141e";
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature(
                "slice(bytes,uint256,uint256)", input, uint256(3), uint256(1)
            )
        );
        require(!ok, "start>end slice should revert");
        require(ret.length == 0, "start>end returndata must be empty");
    }

    // In-bounds slice returns the correct sub-array (value neighbor).
    function testInBoundsSliceValue() public view {
        bytes memory input = hex"0a141e2832"; // [10,20,30,40,50]
        bytes memory got = target.slice(input, 1, 4);
        require(got.length == 3, "in-bounds slice length");
        require(
            uint8(got[0]) == 20 && uint8(got[1]) == 30 && uint8(got[2]) == 40,
            "in-bounds slice value"
        );
    }

    // Regular byte INDEX OOB still panics 0x32 (36-byte Panic(uint256) returndata).
    function testIndexOobPanic32() public {
        bytes memory input = hex"0a141e";
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature(
                "indexAt(bytes,uint256)", input, uint256(10)
            )
        );
        require(!ok, "index OOB should revert");
        require(ret.length == 36, "Panic(0x32) returndata length");
        require(
            keccak256(ret)
                == keccak256(abi.encodeWithSignature("Panic(uint256)", uint256(0x32))),
            "index OOB must be Panic(0x32)"
        );
    }
}
