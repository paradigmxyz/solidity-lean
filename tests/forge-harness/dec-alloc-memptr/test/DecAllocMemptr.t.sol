// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

import "../src/DecAllocMemptr.sol";

contract DecAllocMemptrForgeTest {
    DecAllocMemptr private target;

    // uint256[] band: 32*n + 32 = 2^64 - 32 <= 2^64-1 (raw bound does NOT
    // overflow), but 0x80 + 32*n + 32 = 2^64 + 96 > 2^64-1 -> solc Panic(0x41).
    uint256 private constant ARRAY_BAND = 576460752303423486;

    // bytes band: n + 32 = 2^64 - 1 <= 2^64-1 (raw bound does NOT overflow), but
    // 0x80 + roundUp(n) + 32 overflows 2^64-1 -> solc Panic(0x41).
    uint256 private constant BYTES_BAND = 18446744073709551583; // 2^64 - 33

    function setUp() public {
        target = new DecAllocMemptr();
    }

    function bandArgs(uint256 length) internal pure returns (bytes memory) {
        return bytes.concat(bytes32(uint256(0x20)), bytes32(length));
    }

    function panic0x41() internal pure returns (bytes memory) {
        return abi.encodeWithSignature("Panic(uint256)", uint256(0x41));
    }

    // EAGER `uint256[] memory`, band length -> Panic(0x41) (memPtr term).
    function testMemoryUintArrayBandLengthPanics() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                DecAllocMemptr.memUintArrayLength.selector,
                bandArgs(ARRAY_BAND)
            )
        );
        require(!success, "mem uint[] band should revert");
        require(
            keccak256(output) == keccak256(panic0x41()),
            "mem uint[] band should Panic(0x41)"
        );
    }

    // CONTROL: LAZY `uint256[] calldata`, SAME band length -> empty revert.
    function testCalldataUintArrayBandLengthEmptyRevert() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                DecAllocMemptr.calldataUintArrayLength.selector,
                bandArgs(ARRAY_BAND)
            )
        );
        require(!success, "calldata uint[] band should revert");
        require(output.length == 0, "calldata uint[] band should be empty");
    }

    // EAGER `bytes memory`, band length -> Panic(0x41) (roundUp + memPtr terms).
    function testMemoryBytesBandLengthPanics() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                DecAllocMemptr.memBytesLength.selector,
                bandArgs(BYTES_BAND)
            )
        );
        require(!success, "mem bytes band should revert");
        require(
            keccak256(output) == keccak256(panic0x41()),
            "mem bytes band should Panic(0x41)"
        );
    }

    // CONTROL: LAZY `bytes calldata`, SAME band length -> empty revert.
    function testCalldataBytesBandLengthEmptyRevert() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                DecAllocMemptr.calldataBytesLength.selector,
                bandArgs(BYTES_BAND)
            )
        );
        require(!success, "calldata bytes band should revert");
        require(output.length == 0, "calldata bytes band should be empty");
    }

    // CONTROL: a well-formed EAGER `uint256[] memory` decode is unchanged (the
    // memPtr/roundUp terms do not over-panic a normal small length).
    function testMemoryUintArrayValidDecode() public {
        uint256[] memory a = new uint256[](3);
        a[0] = 10;
        a[1] = 20;
        a[2] = 30;
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                DecAllocMemptr.memUintArrayLength.selector,
                abi.encode(a)
            )
        );
        require(success, "valid mem uint[] should succeed");
        require(abi.decode(output, (uint256)) == 3, "length should be 3");
    }
}
