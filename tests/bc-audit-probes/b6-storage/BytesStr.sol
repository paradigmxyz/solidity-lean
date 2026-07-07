// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract BytesStr {
    string s;
    bytes b;
    function setStr(string calldata v) external { s = v; }
    function getStr() external view returns (string memory) { return s; }
    function getStrLen() external view returns (uint256) { return bytes(s).length; }
    function setBytes(bytes calldata v) external { b = v; }
    function getBytesLen() external view returns (uint256) { return b.length; }
    function getByteAt(uint256 i) external view returns (bytes1) { return b[i]; }
}
