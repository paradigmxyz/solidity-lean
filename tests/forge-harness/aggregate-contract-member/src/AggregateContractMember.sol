// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface IThing {
    function ping() external;
}

// AGG2: a contract/interface-typed storage member is a 20-byte address value.
//  (a) a contract-typed state var packs into the 20 high bytes of a slot;
//  (b) a struct with a contract-typed field spans the real number of slots and
//      its fields are keccak/offset addressed (not the FNV fallback);
//  (c) mapping(ContractType => V) hashes the key as `keccak256(pad32(addr) . slot)`.
contract AggregateContractMemberHarnessTarget {
    uint96 private u;                       // slot 0 offset 0
    IThing private c;                       // slot 0 offset 12 (packs, 20 bytes)
    uint8 private z;                        // slot 1 offset 0

    struct S {
        IThing t;                           // struct slot 0 offset 0
        uint256 x;                          // struct slot 1 offset 0
    }

    S private s;                            // slot 2..3 (2-slot span)
    uint256 private afterS;                 // slot 4
    mapping(IThing => uint256) private mc;  // slot 5

    function setAll() external returns (uint256) {
        u = 0xABCD;
        c = IThing(address(0xAA));
        z = 0x77;
        s.t = IThing(address(0xBB));
        s.x = 0x1234;
        afterS = 0x9999;
        mc[IThing(address(0xCC))] = 0x555;
        return afterS;
    }

    function readAll()
        external
        view
        returns (uint96, address, uint8, address, uint256, uint256, uint256)
    {
        return (u, address(c), z, address(s.t), s.x, afterS, mc[IThing(address(0xCC))]);
    }
}
