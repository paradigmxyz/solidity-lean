// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
type MyInt is uint256;
using {addMI as +, unwrapMI} for MyInt global;
function addMI(MyInt a, MyInt b) pure returns (MyInt) {
    return MyInt.wrap(MyInt.unwrap(a) + MyInt.unwrap(b));
}
function unwrapMI(MyInt a) pure returns (uint256) { return MyInt.unwrap(a); }
contract UDVT {
    function useOp(uint256 x, uint256 y) external pure returns (uint256) {
        MyInt a = MyInt.wrap(x);
        MyInt b = MyInt.wrap(y);
        MyInt c = a + b;                 // operator overload
        return MyInt.unwrap(c);
    }
}
