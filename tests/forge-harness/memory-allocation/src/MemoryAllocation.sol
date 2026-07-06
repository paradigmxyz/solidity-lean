// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryAllocation {
    function allocate(uint256 len)
        external
        pure
        returns (uint256, uint256, uint256, uint256)
    {
        uint256[] memory values = new uint256[](len);
        values[1] = 7;
        return (values.length, values[0], values[1], values[2]);
    }

    function allocateBytes(uint256 len)
        external
        pure
        returns (bytes memory, uint256, uint256, uint256, uint256)
    {
        bytes memory data = new bytes(len);
        data[1] = bytes1(uint8(0xab));
        return (data, data.length, uint8(data[0]), uint8(data[1]), uint8(data[2]));
    }

    function allocateString(uint256 len)
        external
        pure
        returns (string memory, uint256)
    {
        string memory text = new string(len);
        return (text, bytes(text).length);
    }

    function nestedArrayDefaults()
        external
        pure
        returns (uint256, uint256, uint256)
    {
        uint256[][] memory matrix = new uint256[][](2);
        matrix[0] = new uint256[](2);
        matrix[0][1] = 9;
        return (matrix.length, matrix[0][0], matrix[0][1]);
    }
}
