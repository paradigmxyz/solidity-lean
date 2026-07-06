// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract EntrypointSliceControlHarnessTarget {
    uint256 public seen;

    receive() external payable {
        seen = msg.value;
    }

    fallback() external payable {
        seen = msg.data.length;
    }

    function slice(bytes calldata input, uint256 start, uint256 stop)
        external
        pure
        returns (bytes memory)
    {
        return input[start:stop];
    }

    function prefixes(bytes calldata input)
        external
        pure
        returns (bytes memory head, bytes memory tail)
    {
        return (input[:2], input[2:]);
    }

    function sliceByte(bytes calldata input) external pure returns (bytes1) {
        return input[1:3][0];
    }

    function sliceLocalLength(bytes calldata input)
        external
        pure
        returns (uint256)
    {
        bytes calldata local = input[1:3];
        return local.length;
    }

    function sliceMemoryLocalLength(bytes calldata input)
        external
        pure
        returns (uint256)
    {
        bytes memory local = input[1:3];
        return local.length;
    }

    function sliceMemoryLocalMutation(bytes calldata input)
        external
        pure
        returns (bytes1, bytes1)
    {
        bytes memory local = input[1:3];
        local[0] = bytes1(uint8(0xff));
        return (local[0], input[1]);
    }

    function stringSlice(string calldata input, uint256 start, uint256 stop)
        external
        pure
        returns (string memory)
    {
        return input[start:stop];
    }

    function stringPrefixes(string calldata input)
        external
        pure
        returns (string memory head, string memory tail)
    {
        return (input[:2], input[2:]);
    }

    function stringSliceLocal(string calldata input)
        external
        pure
        returns (string memory)
    {
        string calldata local = input[1:3];
        return local;
    }

    function stringSliceMemoryLocal(string calldata input)
        external
        pure
        returns (string memory)
    {
        string memory local = input[1:3];
        return local;
    }

    function arraySlice(
        uint256[] calldata input,
        uint256 start,
        uint256 stop
    ) external pure returns (uint256[] memory) {
        return input[start:stop];
    }

    function arrayPrefixes(uint256[] calldata input)
        external
        pure
        returns (uint256[] memory head, uint256[] memory tail)
    {
        return (input[:2], input[2:]);
    }

    function arraySliceFirst(uint256[] calldata input)
        external
        pure
        returns (uint256)
    {
        return input[1:3][0];
    }

    function arraySliceLocalFirst(uint256[] calldata input)
        external
        pure
        returns (uint256)
    {
        uint256[] calldata local = input[1:3];
        return local[0];
    }

    function arraySliceMemoryLocalFirst(uint256[] calldata input)
        external
        pure
        returns (uint256)
    {
        uint256[] memory local = input[1:3];
        return local[0];
    }

    function arraySliceMemoryLocalMutation(uint256[] calldata input)
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory local = input[1:3];
        local[0] = 99;
        return (local[0], input[1]);
    }

    function loop(uint256 n) external pure returns (uint256) {
        uint256 i;
        uint256 total;
        do {
            total += i;
            i++;
        } while (i < n);
        return total;
    }
}
