// SPDX-License-Identifier: MIT
// #201 BUILTIN-ARG-NARROW-CLEANUP-RESIDUE: the Stage-D (#193/#194) fix wired
// the env-aware abi/builtin argument cleanup into RETURN position and plain
// assignment only; these probes pin the residue positions (assignment RHS,
// vardecl init, require/assert condition, emit args, revert custom-error args,
// nested builtin-in-builtin, compound-assign/delete lvalue keys) where narrow
// (uint8) checked arithmetic inside a builtin argument must Panic 0x11 at the
// operand width on solc 0.8.35 + the EVM.
pragma solidity 0.8.35;

contract BuiltinArgResidue {
    event EB(bytes d);
    event EH(bytes32 h);
    event EMix(uint8 x, uint256 y);
    error Err(bytes d);

    bytes public s;
    uint256 public cnt;
    uint256[] public arr;
    mapping(uint256 => mapping(uint256 => uint256)) public m;

    struct S { uint256[] a; }
    S internal st;

    constructor() {
        for (uint256 i = 0; i < 400; i++) { arr.push(i); }
        for (uint256 i = 0; i < 400; i++) { st.a.push(i); }
    }

    // ---- CONTROLS (already matched before #201; must stay matched) ----
    function ctrlReturn(uint8 a, uint8 b) external pure returns (bytes memory) {
        return abi.encode(a + b);
    }
    function ctrlStmt(uint8 a, uint8 b) external pure returns (uint8) {
        uint8 c = a + b;
        return c;
    }
    function ctrlSafe(uint8 a, uint8 b) external pure returns (bytes memory) {
        // safe values only
        return abi.encode(a + b);
    }

    // ---- A. assignment RHS ----
    function asgLocal(uint8 a, uint8 b) external pure returns (uint256) {
        bytes memory z;
        z = abi.encode(a + b);
        return z.length;
    }
    function asgHash(uint8 a, uint8 b) external pure returns (bytes32) {
        bytes32 h;
        h = keccak256(abi.encodePacked(a + b));
        return h;
    }
    function asgConcat(uint8 a, uint8 b) external pure returns (uint256) {
        bytes memory z;
        z = bytes.concat(bytes1(a + b));
        return z.length;
    }
    function asgStorage(uint8 a, uint8 b) external returns (uint256) {
        s = abi.encodePacked(a + b);
        return s.length;
    }

    // ---- B. vardecl init ----
    function vdBytes(uint8 a, uint8 b) external pure returns (uint256) {
        bytes memory z = abi.encode(a + b);
        return z.length;
    }
    function vdHash(uint8 a, uint8 b) external pure returns (bytes32) {
        bytes32 h = keccak256(abi.encodePacked(a + b));
        return h;
    }
    function vdNested(uint8 a, uint8 b) external pure returns (uint256) {
        uint256 c = uint256(keccak256(abi.encode(a + b)));
        return c % 7;
    }

    // ---- C. require / assert condition ----
    function reqHash(uint8 a, uint8 b, bytes32 h) external pure returns (bool) {
        require(keccak256(abi.encodePacked(a + b)) == h, "no");
        return true;
    }
    function reqEnc(uint8 a, uint8 b) external pure returns (bool) {
        require(abi.encode(a + b).length > 0, "no");
        return true;
    }
    function assertHash(uint8 a, uint8 b, bytes32 h) external pure returns (bool) {
        assert(keccak256(abi.encodePacked(a + b)) != h);
        return true;
    }

    // ---- D. emit args ----
    function emitEnc(uint8 a, uint8 b) external returns (bool) {
        emit EB(abi.encode(a + b));
        return true;
    }
    function emitHash(uint8 a, uint8 b) external returns (bool) {
        emit EH(keccak256(abi.encodePacked(a + b)));
        return true;
    }

    // ---- E. revert custom-error arg ----
    function revErr(uint8 a, uint8 b) external pure returns (bool) {
        revert Err(abi.encode(a + b));
    }

    // ---- controls: function-call arg (Stage-D green) ----
    function sinkB(bytes memory d) internal pure returns (uint256) { return d.length; }
    function sinkH(bytes32 h) internal pure returns (bytes32) { return h; }
    function callEnc(uint8 a, uint8 b) external pure returns (uint256) {
        return sinkB(abi.encode(a + b));
    }
    function callHash(uint8 a, uint8 b) external pure returns (bytes32) {
        return sinkH(keccak256(abi.encodePacked(a + b)));
    }

    // ---- F. nested builtin-in-builtin ----
    function nestConcat(uint8 a, uint8 b) external pure returns (bytes32) {
        return keccak256(bytes.concat(abi.encode(a + b)));
    }
    function nestEnc(uint8 a, uint8 b) external pure returns (uint256) {
        bytes memory z = abi.encode(abi.encodePacked(a + b));
        return z.length;
    }

    // ---- D. emit mixed pure + call args (panic BEFORE the call runs) ----
    function bump() internal returns (uint256) { cnt = cnt + 1; return cnt; }
    function emitMix(uint8 a, uint8 b) external returns (uint256) {
        emit EMix(a + b, bump());
        return cnt;
    }

    event EO(uint256 x, uint256 y);
    function emitOrder() external returns (uint256) {
        emit EO(cnt, bump());
        return cnt;
    }

    // ---- G. lvalue index-key residue ----
    function lvStruct(uint8 a, uint8 b, uint256 v) external returns (uint256) {
        st.a[a + b] = v;
        return st.a[0];
    }
    function lvMapDeep(uint8 a, uint8 b, uint256 k1, uint256 v) external returns (uint256) {
        m[k1][a + b] = v;
        return m[k1][300];
    }
    function lvCompound(uint8 a, uint8 b) external returns (uint256) {
        arr[a + b] += 1;
        return arr[300];
    }
    function lvDelete(uint8 a, uint8 b) external returns (uint256) {
        delete arr[a + b];
        return arr[300];
    }
}
