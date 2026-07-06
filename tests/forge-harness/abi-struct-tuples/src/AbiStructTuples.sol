// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract AbiStructTuplesHarnessTarget {
    struct Pair {
        uint256 a;
        bytes b;
    }

    function encodePair(uint256 a, bytes memory payload)
        external
        pure
        returns (bytes memory)
    {
        return abi.encode(Pair({a: a, b: payload}));
    }

    function decodePair(bytes memory encoded)
        external
        pure
        returns (uint256, uint256)
    {
        Pair memory pair = abi.decode(encoded, (Pair));
        return (pair.a, pair.b.length);
    }

    function roundTrip(uint256 a, bytes memory payload)
        external
        pure
        returns (uint256, uint256)
    {
        Pair memory pair = abi.decode(
            abi.encode(Pair({a: a, b: payload})),
            (Pair)
        );
        return (pair.a, pair.b.length);
    }
}
