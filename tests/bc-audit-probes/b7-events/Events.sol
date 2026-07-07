// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Events {
    enum E { A, B, C }

    event Plain(uint256 a, uint256 b);        // topic0 keccak256("Plain(uint256,uint256)")
    event Narrow(uint8 indexed a, uint16 b);  // topic0 keccak256("Narrow(uint8,uint16)"), topic1 = padded a
    event StrIdx(string indexed s);           // topic0 keccak256("StrIdx(string)"), topic1 = keccak256("hello")
    event Anon(uint256 a) anonymous;          // no topic0
    event ArrIdx(uint256[] indexed xs);       // topic1 = keccak256(0xaa|0xbb padded)
    event NegIdx(int8 indexed v);             // topic1 = sign-extended 32-byte

    error Bad(uint256 x);
    error Empty();

    function emitPlain() external { emit Plain(1, 2); }
    function emitNarrow() external { emit Narrow(0x12, 0x3456); }
    function emitStr() external { emit StrIdx("hello"); }
    function emitAnon() external { emit Anon(7); }
    function emitArr() external {
        uint256[] memory xs = new uint256[](2);
        xs[0] = 0xaa; xs[1] = 0xbb;
        emit ArrIdx(xs);
    }
    function emitNeg() external { emit NegIdx(int8(-1)); }

    function revBad() external pure { revert Bad(0x99); }
    function revEmpty() external pure { revert Empty(); }

    function panicDiv(uint256 x) external pure returns (uint256) { return uint256(100) / x; }
    function panicAssert() external pure { assert(false); }
    function panicEnum(uint256 v) external pure returns (E) { return E(v); }
}
