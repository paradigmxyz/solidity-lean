// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

// Import-inlined, assembly-free adaptation of selected paths from
// OpenZeppelin Contracts v5.6.1 `access/AccessControl.sol`,
// `access/extensions/AccessControlEnumerable.sol`, `utils/Context.sol`,
// `utils/introspection/ERC165.sol`, and `utils/structs/EnumerableSet.sol`.
// The upstream `values()` helpers are omitted because they use memory-layout
// assembly, which is outside this source layer.
interface OpenZeppelinEnumerableIERC165 {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

abstract contract OpenZeppelinEnumerableERC165 is
    OpenZeppelinEnumerableIERC165
{
    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        returns (bool)
    {
        return interfaceId == type(OpenZeppelinEnumerableIERC165).interfaceId;
    }
}

interface OpenZeppelinEnumerableIAccessControl {
    error AccessControlUnauthorizedAccount(address account, bytes32 neededRole);
    error AccessControlBadConfirmation();

    event RoleAdminChanged(
        bytes32 indexed role,
        bytes32 indexed previousAdminRole,
        bytes32 indexed newAdminRole
    );
    event RoleGranted(
        bytes32 indexed role,
        address indexed account,
        address indexed sender
    );
    event RoleRevoked(
        bytes32 indexed role,
        address indexed account,
        address indexed sender
    );

    function hasRole(bytes32 role, address account)
        external
        view
        returns (bool);

    function getRoleAdmin(bytes32 role) external view returns (bytes32);

    function grantRole(bytes32 role, address account) external;

    function revokeRole(bytes32 role, address account) external;

    function renounceRole(bytes32 role, address callerConfirmation) external;
}

interface OpenZeppelinEnumerableIAccessControlEnumerable is
    OpenZeppelinEnumerableIAccessControl
{
    function getRoleMember(bytes32 role, uint256 index)
        external
        view
        returns (address);

    function getRoleMemberCount(bytes32 role)
        external
        view
        returns (uint256);
}

abstract contract OpenZeppelinAccessControlEnumerableContext {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

abstract contract OpenZeppelinAccessControlEnumerableBase is
    OpenZeppelinAccessControlEnumerableContext,
    OpenZeppelinEnumerableIAccessControl,
    OpenZeppelinEnumerableERC165
{
    struct RoleData {
        mapping(address account => bool) hasRole;
        bytes32 adminRole;
    }

    mapping(bytes32 role => RoleData) private _roles;

    bytes32 public constant DEFAULT_ADMIN_ROLE = 0x00;

    modifier onlyRole(bytes32 role) {
        _checkRole(role);
        _;
    }

    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        override
        returns (bool)
    {
        return
            interfaceId ==
            type(OpenZeppelinEnumerableIAccessControl).interfaceId ||
            super.supportsInterface(interfaceId);
    }

    function hasRole(bytes32 role, address account)
        public
        view
        virtual
        returns (bool)
    {
        return _roles[role].hasRole[account];
    }

    function _checkRole(bytes32 role) internal view virtual {
        _checkRole(role, _msgSender());
    }

    function _checkRole(bytes32 role, address account) internal view virtual {
        if (!hasRole(role, account)) {
            revert AccessControlUnauthorizedAccount(account, role);
        }
    }

    function getRoleAdmin(bytes32 role)
        public
        view
        virtual
        returns (bytes32)
    {
        return _roles[role].adminRole;
    }

    function grantRole(bytes32 role, address account)
        public
        virtual
        onlyRole(getRoleAdmin(role))
    {
        _grantRole(role, account);
    }

    function revokeRole(bytes32 role, address account)
        public
        virtual
        onlyRole(getRoleAdmin(role))
    {
        _revokeRole(role, account);
    }

    function renounceRole(bytes32 role, address callerConfirmation)
        public
        virtual
    {
        if (callerConfirmation != _msgSender()) {
            revert AccessControlBadConfirmation();
        }

        _revokeRole(role, callerConfirmation);
    }

    function _setRoleAdmin(bytes32 role, bytes32 adminRole) internal virtual {
        bytes32 previousAdminRole = getRoleAdmin(role);
        _roles[role].adminRole = adminRole;
        emit RoleAdminChanged(role, previousAdminRole, adminRole);
    }

    function _grantRole(bytes32 role, address account)
        internal
        virtual
        returns (bool)
    {
        if (!hasRole(role, account)) {
            _roles[role].hasRole[account] = true;
            emit RoleGranted(role, account, _msgSender());
            return true;
        } else {
            return false;
        }
    }

    function _revokeRole(bytes32 role, address account)
        internal
        virtual
        returns (bool)
    {
        if (hasRole(role, account)) {
            _roles[role].hasRole[account] = false;
            emit RoleRevoked(role, account, _msgSender());
            return true;
        } else {
            return false;
        }
    }
}

library OpenZeppelinAccessControlEnumerableSet {
    struct Set {
        bytes32[] _values;
        mapping(bytes32 value => uint256) _positions;
    }

    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            set._positions[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    function _remove(Set storage set, bytes32 value) private returns (bool) {
        uint256 position = set._positions[value];

        if (position != 0) {
            uint256 valueIndex = position - 1;
            uint256 lastIndex = set._values.length - 1;

            if (valueIndex != lastIndex) {
                bytes32 lastValue = set._values[lastIndex];
                set._values[valueIndex] = lastValue;
                set._positions[lastValue] = position;
            }

            set._values.pop();
            delete set._positions[value];

            return true;
        } else {
            return false;
        }
    }

    function _contains(Set storage set, bytes32 value)
        private
        view
        returns (bool)
    {
        return set._positions[value] != 0;
    }

    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

    function _at(Set storage set, uint256 index)
        private
        view
        returns (bytes32)
    {
        return set._values[index];
    }

    struct AddressSet {
        Set _inner;
    }

    function add(AddressSet storage set, address value)
        internal
        returns (bool)
    {
        return _add(set._inner, bytes32(uint256(uint160(value))));
    }

    function remove(AddressSet storage set, address value)
        internal
        returns (bool)
    {
        return _remove(set._inner, bytes32(uint256(uint160(value))));
    }

    function contains(AddressSet storage set, address value)
        internal
        view
        returns (bool)
    {
        return _contains(set._inner, bytes32(uint256(uint160(value))));
    }

    function length(AddressSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    function at(AddressSet storage set, uint256 index)
        internal
        view
        returns (address)
    {
        return address(uint160(uint256(_at(set._inner, index))));
    }
}

abstract contract OpenZeppelinAccessControlEnumerable is
    OpenZeppelinEnumerableIAccessControlEnumerable,
    OpenZeppelinAccessControlEnumerableBase
{
    using OpenZeppelinAccessControlEnumerableSet
        for OpenZeppelinAccessControlEnumerableSet.AddressSet;

    mapping(bytes32 role => OpenZeppelinAccessControlEnumerableSet.AddressSet)
        private _roleMembers;

    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        override
        returns (bool)
    {
        return
            interfaceId ==
            type(OpenZeppelinEnumerableIAccessControlEnumerable).interfaceId ||
            super.supportsInterface(interfaceId);
    }

    function getRoleMember(bytes32 role, uint256 index)
        public
        view
        virtual
        returns (address)
    {
        return _roleMembers[role].at(index);
    }

    function getRoleMemberCount(bytes32 role)
        public
        view
        virtual
        returns (uint256)
    {
        return _roleMembers[role].length();
    }

    function _grantRole(bytes32 role, address account)
        internal
        virtual
        override
        returns (bool)
    {
        bool granted = super._grantRole(role, account);
        if (granted) {
            _roleMembers[role].add(account);
        }
        return granted;
    }

    function _revokeRole(bytes32 role, address account)
        internal
        virtual
        override
        returns (bool)
    {
        bool revoked = super._revokeRole(role, account);
        if (revoked) {
            _roleMembers[role].remove(account);
        }
        return revoked;
    }
}

contract OpenZeppelinAccessControlEnumerableHarness is
    OpenZeppelinAccessControlEnumerable
{
    bytes32 public constant WRITER_ROLE =
        0x0000000000000000000000000000000000000000000000000000000000001234;
    bytes32 public constant MANAGER_ROLE =
        0x0000000000000000000000000000000000000000000000000000000000005678;

    uint256 public writes;

    constructor(address admin) {
        _grantRole(DEFAULT_ADMIN_ROLE, admin);
    }

    function touch() public onlyRole(WRITER_ROLE) returns (uint256) {
        writes += 1;
        return writes;
    }

    function setWriterAdmin(bytes32 adminRole)
        public
        onlyRole(DEFAULT_ADMIN_ROLE)
    {
        _setRoleAdmin(WRITER_ROLE, adminRole);
    }

    function seedWriters(address first, address second, address third)
        external
        returns (uint256)
    {
        _grantRole(WRITER_ROLE, first);
        _grantRole(WRITER_ROLE, second);
        _grantRole(WRITER_ROLE, third);
        return getRoleMemberCount(WRITER_ROLE);
    }
}

contract OpenZeppelinAccessControlEnumerableForwarder {
    function grant(
        OpenZeppelinAccessControlEnumerableHarness target,
        bytes32 role,
        address account
    ) external {
        target.grantRole(role, account);
    }

    function revoke(
        OpenZeppelinAccessControlEnumerableHarness target,
        bytes32 role,
        address account
    ) external {
        target.revokeRole(role, account);
    }

    function renounce(
        OpenZeppelinAccessControlEnumerableHarness target,
        bytes32 role,
        address confirmation
    ) external {
        target.renounceRole(role, confirmation);
    }

    function touch(OpenZeppelinAccessControlEnumerableHarness target)
        external
        returns (uint256)
    {
        return target.touch();
    }
}
