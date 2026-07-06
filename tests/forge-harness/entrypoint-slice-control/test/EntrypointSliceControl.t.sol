// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/EntrypointSliceControl.sol";

contract EntrypointSliceControlForgeTest {
    function testReceiveAndFallback() public {
        EntrypointSliceControlHarnessTarget target =
            new EntrypointSliceControlHarnessTarget();

        (bool ok,) = address(target).call{value: 7}("");
        require(ok, "receive");
        require(target.seen() == 7, "received");

        (ok,) = address(target).call(hex"0102030405");
        require(ok, "fallback");
        require(target.seen() == 5, "fallback length");
    }

    function testSlices() public {
        EntrypointSliceControlHarnessTarget target =
            new EntrypointSliceControlHarnessTarget();

        bytes memory middle = target.slice(hex"0a141e2832", 1, 4);
        require(
            keccak256(middle) == keccak256(bytes(hex"141e28")),
            "middle"
        );

        (bytes memory head, bytes memory tail) = target.prefixes(hex"01020304");
        require(keccak256(head) == keccak256(bytes(hex"0102")), "head");
        require(keccak256(tail) == keccak256(bytes(hex"0304")), "tail");
        require(target.sliceByte(hex"0a141e28") == 0x14, "slice byte");
        require(target.sliceLocalLength(hex"0a141e28") == 2, "slice local");
        require(
            target.sliceMemoryLocalLength(hex"0a141e28") == 2,
            "slice memory local"
        );

        string memory middleText = target.stringSlice("abcdef", 1, 4);
        require(
            keccak256(bytes(middleText)) == keccak256(bytes("bcd")),
            "string middle"
        );

        (string memory headText, string memory tailText) =
            target.stringPrefixes("wxyz");
        require(
            keccak256(bytes(headText)) == keccak256(bytes("wx")),
            "string head"
        );
        require(
            keccak256(bytes(tailText)) == keccak256(bytes("yz")),
            "string tail"
        );
        string memory localText = target.stringSliceLocal("abcdef");
        require(
            keccak256(bytes(localText)) == keccak256(bytes("bc")),
            "string local"
        );
        string memory memoryLocalText =
            target.stringSliceMemoryLocal("abcdef");
        require(
            keccak256(bytes(memoryLocalText)) == keccak256(bytes("bc")),
            "string memory local"
        );

        uint256[] memory values = new uint256[](4);
        values[0] = 10;
        values[1] = 20;
        values[2] = 30;
        values[3] = 40;

        uint256[] memory middleArray = target.arraySlice(values, 1, 3);
        require(middleArray.length == 2, "array middle length");
        require(middleArray[0] == 20, "array middle first");
        require(middleArray[1] == 30, "array middle second");

        (uint256[] memory headArray, uint256[] memory tailArray) =
            target.arrayPrefixes(values);
        require(headArray.length == 2, "array head length");
        require(headArray[0] == 10, "array head first");
        require(headArray[1] == 20, "array head second");
        require(tailArray.length == 2, "array tail length");
        require(tailArray[0] == 30, "array tail first");
        require(tailArray[1] == 40, "array tail second");
        require(target.arraySliceFirst(values) == 20, "array slice first");
        require(
            target.arraySliceLocalFirst(values) == 20,
            "array local first"
        );
        require(
            target.arraySliceMemoryLocalFirst(values) == 20,
            "array memory local first"
        );
    }

    function testSliceMemoryLocalMutation() public {
        EntrypointSliceControlHarnessTarget target =
            new EntrypointSliceControlHarnessTarget();

        (bytes1 mutatedByte, bytes1 sourceByte) =
            target.sliceMemoryLocalMutation(hex"0a141e28");
        require(mutatedByte == 0xff, "slice memory mutated byte");
        require(sourceByte == 0x14, "slice memory source byte");

        uint256[] memory values = new uint256[](4);
        values[0] = 10;
        values[1] = 20;
        values[2] = 30;
        values[3] = 40;

        (uint256 mutatedArray, uint256 sourceArray) =
            target.arraySliceMemoryLocalMutation(values);
        require(mutatedArray == 99, "array memory mutated");
        require(sourceArray == 20, "array memory source");
    }

    function testDoWhile() public {
        EntrypointSliceControlHarnessTarget target =
            new EntrypointSliceControlHarnessTarget();

        require(target.loop(5) == 10, "loop 5");
        require(target.loop(0) == 0, "loop 0");
    }
}
