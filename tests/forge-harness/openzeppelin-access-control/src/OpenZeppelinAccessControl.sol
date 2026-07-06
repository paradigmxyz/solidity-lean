// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface OpenZeppelinIERC165 {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

abstract contract OpenZeppelinERC165 is OpenZeppelinIERC165 {
    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        returns (bool)
    {
        return interfaceId == type(OpenZeppelinIERC165).interfaceId;
    }
}

interface OpenZeppelinIAccessControl {
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

abstract contract OpenZeppelinAccessControlContext {
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

abstract contract OpenZeppelinAccessControl is
    OpenZeppelinAccessControlContext,
    OpenZeppelinIAccessControl,
    OpenZeppelinERC165
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
            interfaceId == type(OpenZeppelinIAccessControl).interfaceId ||
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

contract OpenZeppelinAccessControlHarness is OpenZeppelinAccessControl {
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
}

contract OpenZeppelinAccessControlForwarder {
    function grant(
        OpenZeppelinAccessControlHarness target,
        bytes32 role,
        address account
    ) external {
        target.grantRole(role, account);
    }

    function revoke(
        OpenZeppelinAccessControlHarness target,
        bytes32 role,
        address account
    ) external {
        target.revokeRole(role, account);
    }

    function renounce(
        OpenZeppelinAccessControlHarness target,
        bytes32 role,
        address confirmation
    ) external {
        target.renounceRole(role, confirmation);
    }

    function touch(OpenZeppelinAccessControlHarness target)
        external
        returns (uint256)
    {
        return target.touch();
    }
}
