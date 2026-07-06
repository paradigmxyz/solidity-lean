#!/usr/bin/env python3
"""Render solc Solidity AST as Lean source-semantics AST.

This is a harness frontend, not trusted semantics.  It asks pinned solc for the
analyzed Solidity AST, translates the supported source nodes into
`SolidCore.Solidity` syntax, and then the normal Lean checker/interpreter must
accept and execute the result.
"""

from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any, Sequence


class ImportError(Exception):
    pass


FUNCTION_PARAM_COUNT_BY_ID: dict[int, int] = {}


SUPPORTED_NODE_TYPES: set[str] = {'Assignment', 'ArrayTypeName', 'BinaryOperation', 'Block', 'Break', 'Conditional', 'Continue', 'ContractDefinition', 'DoWhileStatement', 'ElementaryTypeName', 'ElementaryTypeNameExpression', 'EmitStatement', 'EnumDefinition', 'EnumValue', 'ErrorDefinition', 'EventDefinition', 'ExpressionStatement', 'ForStatement', 'FunctionCall', 'FunctionCallOptions', 'FunctionDefinition', 'FunctionTypeName', 'Identifier', 'IdentifierPath', 'IfStatement', 'IndexAccess', 'IndexRangeAccess', 'InheritanceSpecifier', 'Literal', 'Mapping', 'MemberAccess', 'ModifierDefinition', 'ModifierInvocation', 'NewExpression', 'OverrideSpecifier', 'ParameterList', 'PlaceholderStatement', 'PragmaDirective', 'Return', 'RevertStatement', 'SourceUnit', 'StructDefinition', 'TupleExpression', 'TryCatchClause', 'TryStatement', 'UncheckedBlock', 'UnaryOperation', 'UserDefinedTypeName', 'UserDefinedValueTypeDefinition', 'UsingForDirective', 'VariableDeclaration', 'VariableDeclarationStatement', 'WhileStatement'}
METADATA_NODE_TYPES: set[str] = {'StructuredDocumentation'}
EXCLUDED_NODE_TYPES: dict[str, str] = {'ImportDirective': 'import resolution is intentionally out of scope', 'InlineAssembly': 'inline assembly/Yul is intentionally out of scope'}
SOURCE_CHILD_FIELDS: set[tuple[str, str]] = {('ArrayTypeName', 'baseType'), ('ArrayTypeName', 'length'), ('Assignment', 'leftHandSide'), ('Assignment', 'rightHandSide'), ('BinaryOperation', 'leftExpression'), ('BinaryOperation', 'rightExpression'), ('Block', 'statements'), ('Conditional', 'condition'), ('Conditional', 'falseExpression'), ('Conditional', 'trueExpression'), ('ContractDefinition', 'baseContracts'), ('ContractDefinition', 'nodes'), ('DoWhileStatement', 'body'), ('DoWhileStatement', 'condition'), ('ElementaryTypeNameExpression', 'typeName'), ('EmitStatement', 'eventCall'), ('EnumDefinition', 'members'), ('ErrorDefinition', 'parameters'), ('EventDefinition', 'parameters'), ('ExpressionStatement', 'expression'), ('ForStatement', 'body'), ('ForStatement', 'condition'), ('ForStatement', 'initializationExpression'), ('ForStatement', 'loopExpression'), ('FunctionCall', 'arguments'), ('FunctionCall', 'expression'), ('FunctionCallOptions', 'expression'), ('FunctionCallOptions', 'options'), ('FunctionDefinition', 'body'), ('FunctionDefinition', 'modifiers'), ('FunctionDefinition', 'overrides'), ('FunctionDefinition', 'parameters'), ('FunctionDefinition', 'returnParameters'), ('FunctionTypeName', 'parameterTypes'), ('FunctionTypeName', 'returnParameterTypes'), ('IfStatement', 'condition'), ('IfStatement', 'falseBody'), ('IfStatement', 'trueBody'), ('IndexAccess', 'baseExpression'), ('IndexAccess', 'indexExpression'), ('IndexRangeAccess', 'baseExpression'), ('IndexRangeAccess', 'endExpression'), ('IndexRangeAccess', 'startExpression'), ('InheritanceSpecifier', 'arguments'), ('InheritanceSpecifier', 'baseName'), ('Mapping', 'keyType'), ('Mapping', 'valueType'), ('MemberAccess', 'expression'), ('ModifierDefinition', 'body'), ('ModifierDefinition', 'overrides'), ('ModifierDefinition', 'parameters'), ('ModifierInvocation', 'arguments'), ('ModifierInvocation', 'modifierName'), ('NewExpression', 'typeName'), ('OverrideSpecifier', 'overrides'), ('ParameterList', 'parameters'), ('Return', 'expression'), ('RevertStatement', 'errorCall'), ('SourceUnit', 'nodes'), ('StructDefinition', 'members'), ('TryCatchClause', 'block'), ('TryCatchClause', 'parameters'), ('TryStatement', 'clauses'), ('TryStatement', 'externalCall'), ('TupleExpression', 'components'), ('UnaryOperation', 'subExpression'), ('UncheckedBlock', 'statements'), ('UserDefinedTypeName', 'pathNode'), ('UserDefinedValueTypeDefinition', 'underlyingType'), ('UsingForDirective', 'functionList.definition'), ('UsingForDirective', 'functionList.function'), ('UsingForDirective', 'libraryName'), ('UsingForDirective', 'typeName'), ('VariableDeclaration', 'overrides'), ('VariableDeclaration', 'typeName'), ('VariableDeclaration', 'value'), ('VariableDeclarationStatement', 'declarations'), ('VariableDeclarationStatement', 'initialValue'), ('WhileStatement', 'body'), ('WhileStatement', 'condition')}
METADATA_CHILD_FIELDS: set[tuple[str, str]] = {('ContractDefinition', 'documentation'), ('EnumDefinition', 'documentation'), ('ErrorDefinition', 'documentation'), ('EventDefinition', 'documentation'), ('FunctionDefinition', 'documentation'), ('ModifierDefinition', 'documentation'), ('StructDefinition', 'documentation'), ('VariableDeclaration', 'documentation')}
SOURCE_SCALAR_FIELDS: set[tuple[str, str]] = {('Assignment', 'operator'), ('BinaryOperation', 'operator'), ('ContractDefinition', 'abstract'), ('ContractDefinition', 'contractKind'), ('ContractDefinition', 'name'), ('ElementaryTypeName', 'name'), ('ElementaryTypeName', 'stateMutability'), ('EnumDefinition', 'name'), ('EnumValue', 'name'), ('ErrorDefinition', 'name'), ('EventDefinition', 'anonymous'), ('EventDefinition', 'name'), ('FunctionCall', 'names'), ('FunctionCallOptions', 'names'), ('FunctionDefinition', 'kind'), ('FunctionDefinition', 'name'), ('FunctionDefinition', 'stateMutability'), ('FunctionDefinition', 'virtual'), ('FunctionDefinition', 'visibility'), ('FunctionTypeName', 'stateMutability'), ('FunctionTypeName', 'visibility'), ('Identifier', 'name'), ('IdentifierPath', 'name'), ('Literal', 'hexValue'), ('Literal', 'kind'), ('Literal', 'subdenomination'), ('Literal', 'value'), ('MemberAccess', 'memberName'), ('ModifierDefinition', 'name'), ('ModifierDefinition', 'virtual'), ('PragmaDirective', 'literals'), ('StructDefinition', 'name'), ('TryCatchClause', 'errorName'), ('TupleExpression', 'isInlineArray'), ('UnaryOperation', 'operator'), ('UnaryOperation', 'prefix'), ('UserDefinedValueTypeDefinition', 'name'), ('UsingForDirective', 'functionList.operator'), ('UsingForDirective', 'global'), ('VariableDeclaration', 'constant'), ('VariableDeclaration', 'indexed'), ('VariableDeclaration', 'mutability'), ('VariableDeclaration', 'name'), ('VariableDeclaration', 'stateVariable'), ('VariableDeclaration', 'storageLocation'), ('VariableDeclaration', 'visibility'), ('VariableDeclarationStatement', 'declarations')}
ANALYSIS_SCALAR_FIELDS: set[tuple[str, str]] = {('ArrayTypeName', 'typeDescriptions.typeIdentifier'), ('ArrayTypeName', 'typeDescriptions.typeString'), ('Assignment', 'isConstant'), ('Assignment', 'isLValue'), ('Assignment', 'isPure'), ('Assignment', 'lValueRequested'), ('Assignment', 'typeDescriptions.typeIdentifier'), ('Assignment', 'typeDescriptions.typeString'), ('BinaryOperation', 'commonType.typeIdentifier'), ('BinaryOperation', 'commonType.typeString'), ('BinaryOperation', 'isConstant'), ('BinaryOperation', 'isLValue'), ('BinaryOperation', 'isPure'), ('BinaryOperation', 'lValueRequested'), ('BinaryOperation', 'function'), ('BinaryOperation', 'typeDescriptions.typeIdentifier'), ('BinaryOperation', 'typeDescriptions.typeString'), ('Conditional', 'isConstant'), ('Conditional', 'isLValue'), ('Conditional', 'isPure'), ('Conditional', 'lValueRequested'), ('Conditional', 'typeDescriptions.typeIdentifier'), ('Conditional', 'typeDescriptions.typeString'), ('ContractDefinition', 'fullyImplemented'), ('ElementaryTypeName', 'typeDescriptions.typeIdentifier'), ('ElementaryTypeName', 'typeDescriptions.typeString'), ('ElementaryTypeNameExpression', 'argumentTypes.typeIdentifier'), ('ElementaryTypeNameExpression', 'argumentTypes.typeString'), ('ElementaryTypeNameExpression', 'isConstant'), ('ElementaryTypeNameExpression', 'isLValue'), ('ElementaryTypeNameExpression', 'isPure'), ('ElementaryTypeNameExpression', 'lValueRequested'), ('ElementaryTypeNameExpression', 'typeDescriptions.typeIdentifier'), ('ElementaryTypeNameExpression', 'typeDescriptions.typeString'), ('ForStatement', 'isSimpleCounterLoop'), ('FunctionCall', 'isConstant'), ('FunctionCall', 'isLValue'), ('FunctionCall', 'isPure'), ('FunctionCall', 'kind'), ('FunctionCall', 'lValueRequested'), ('FunctionCall', 'tryCall'), ('FunctionCall', 'typeDescriptions.typeIdentifier'), ('FunctionCall', 'typeDescriptions.typeString'), ('FunctionCallOptions', 'argumentTypes.typeIdentifier'), ('FunctionCallOptions', 'argumentTypes.typeString'), ('FunctionCallOptions', 'isConstant'), ('FunctionCallOptions', 'isLValue'), ('FunctionCallOptions', 'isPure'), ('FunctionCallOptions', 'lValueRequested'), ('FunctionCallOptions', 'typeDescriptions.typeIdentifier'), ('FunctionCallOptions', 'typeDescriptions.typeString'), ('FunctionDefinition', 'implemented'), ('FunctionTypeName', 'typeDescriptions.typeIdentifier'), ('FunctionTypeName', 'typeDescriptions.typeString'), ('Identifier', 'argumentTypes.typeIdentifier'), ('Identifier', 'argumentTypes.typeString'), ('Identifier', 'typeDescriptions.typeIdentifier'), ('Identifier', 'typeDescriptions.typeString'), ('IndexAccess', 'isConstant'), ('IndexAccess', 'isLValue'), ('IndexAccess', 'isPure'), ('IndexAccess', 'lValueRequested'), ('IndexAccess', 'typeDescriptions.typeIdentifier'), ('IndexAccess', 'typeDescriptions.typeString'), ('IndexRangeAccess', 'isConstant'), ('IndexRangeAccess', 'isLValue'), ('IndexRangeAccess', 'isPure'), ('IndexRangeAccess', 'lValueRequested'), ('IndexRangeAccess', 'typeDescriptions.typeIdentifier'), ('IndexRangeAccess', 'typeDescriptions.typeString'), ('Literal', 'isConstant'), ('Literal', 'isLValue'), ('Literal', 'isPure'), ('Literal', 'lValueRequested'), ('Literal', 'typeDescriptions.typeIdentifier'), ('Literal', 'typeDescriptions.typeString'), ('Mapping', 'typeDescriptions.typeIdentifier'), ('Mapping', 'typeDescriptions.typeString'), ('MemberAccess', 'argumentTypes.typeIdentifier'), ('MemberAccess', 'argumentTypes.typeString'), ('MemberAccess', 'isConstant'), ('MemberAccess', 'isLValue'), ('MemberAccess', 'isPure'), ('MemberAccess', 'lValueRequested'), ('MemberAccess', 'typeDescriptions.typeIdentifier'), ('MemberAccess', 'typeDescriptions.typeString'), ('ModifierInvocation', 'kind'), ('NewExpression', 'argumentTypes.typeIdentifier'), ('NewExpression', 'argumentTypes.typeString'), ('NewExpression', 'isConstant'), ('NewExpression', 'isLValue'), ('NewExpression', 'isPure'), ('NewExpression', 'lValueRequested'), ('NewExpression', 'typeDescriptions.typeIdentifier'), ('NewExpression', 'typeDescriptions.typeString'), ('TupleExpression', 'isConstant'), ('TupleExpression', 'isLValue'), ('TupleExpression', 'isPure'), ('TupleExpression', 'lValueRequested'), ('TupleExpression', 'typeDescriptions.typeIdentifier'), ('TupleExpression', 'typeDescriptions.typeString'), ('UnaryOperation', 'function'), ('UnaryOperation', 'isConstant'), ('UnaryOperation', 'isLValue'), ('UnaryOperation', 'isPure'), ('UnaryOperation', 'lValueRequested'), ('UnaryOperation', 'typeDescriptions.typeIdentifier'), ('UnaryOperation', 'typeDescriptions.typeString'), ('UserDefinedTypeName', 'typeDescriptions.typeIdentifier'), ('UserDefinedTypeName', 'typeDescriptions.typeString'), ('VariableDeclaration', 'typeDescriptions.typeIdentifier'), ('VariableDeclaration', 'typeDescriptions.typeString')}
METADATA_SCALAR_FIELDS: set[tuple[str, str]] = {('Mapping', 'keyName'), ('Mapping', 'keyNameLocation'), ('Mapping', 'valueName'), ('Mapping', 'valueNameLocation'), ('ModifierDefinition', 'baseModifiers'), ('ModifierDefinition', 'visibility'), ('SourceUnit', 'absolutePath'), ('SourceUnit', 'license'), ('StructDefinition', 'visibility'), ('StructuredDocumentation', 'text'), ('VariableDeclarationStatement', 'assignments')}
METADATA_SCALAR_FIELD_SUFFIXES: set[str] = {'baseFunctions', 'canonicalName', 'contractDependencies', 'errorSelector', 'eventSelector', 'functionReturnParameters', 'functionSelector', 'id', 'linearizedBaseContracts', 'memberLocation', 'nameLocation', 'nameLocations', 'overloadedDeclarations', 'referencedDeclaration', 'scope', 'src', 'usedErrors', 'usedEvents'}
SOURCE_SCALAR_VALUE_DOMAINS: dict[tuple[str, str], set[Any]] = {
    ('Assignment', 'operator'): {'=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>='},
    ('BinaryOperation', 'operator'): {'+', '-', '*', '/', '%', '**', '==', '!=', '<', '>', '<=', '>=', '&&', '||', '&', '|', '^', '<<', '>>'},
    ('ContractDefinition', 'abstract'): {False, True},
    ('ContractDefinition', 'contractKind'): {'contract', 'interface', 'library'},
    ('ElementaryTypeName', 'stateMutability'): {'nonpayable', 'payable'},
    ('EventDefinition', 'anonymous'): {False, True},
    ('FunctionDefinition', 'kind'): {'constructor', 'fallback', 'freeFunction', 'function', 'receive'},
    ('FunctionDefinition', 'stateMutability'): {'nonpayable', 'payable', 'pure', 'view'},
    ('FunctionDefinition', 'virtual'): {False, True},
    ('FunctionDefinition', 'visibility'): {'external', 'internal', 'private', 'public'},
    ('FunctionTypeName', 'stateMutability'): {'nonpayable', 'payable', 'pure', 'view'},
    ('FunctionTypeName', 'visibility'): {'external', 'internal'},
    ('Literal', 'kind'): {'bool', 'hexString', 'number', 'string', 'unicodeString'},
    ('Literal', 'subdenomination'): {'days', 'ether', 'gwei', 'hours', 'minutes', 'seconds', 'weeks', 'wei'},
    ('TupleExpression', 'isInlineArray'): {False, True},
    ('TryCatchClause', 'errorName'): {'', 'Error', 'Panic'},
    ('UnaryOperation', 'operator'): {'!', '-', '--', '++', 'delete', '~'},
    ('UnaryOperation', 'prefix'): {False, True},
    ('UsingForDirective', 'global'): {False, True},
    ('VariableDeclaration', 'constant'): {False, True},
    ('VariableDeclaration', 'indexed'): {False, True},
    ('VariableDeclaration', 'mutability'): {'constant', 'immutable', 'mutable'},
    ('VariableDeclaration', 'stateVariable'): {False, True},
    ('VariableDeclaration', 'storageLocation'): {'calldata', 'default', 'memory', 'storage', 'transient'},
    ('VariableDeclaration', 'visibility'): {'internal', 'private', 'public'},
}


def fail(message: str) -> None:
    raise ImportError(message)


def resolve_executable(name: str) -> str:
    if "/" in name:
        return name
    return shutil.which(name) or name


def lean_string(value: str) -> str:
    return json.dumps(value)


def lean_list(items: Sequence[str]) -> str:
    return "[" + ", ".join(items) + "]"


def lean_option(value: str | None) -> str:
    if value is None:
        return "none"
    return f"some {value}"


def namespace_segments(namespace: str) -> list[str]:
    segments = namespace.split(".")
    if not segments or any(not re.fullmatch("[A-Za-z_][A-Za-z0-9_']*", s) for s in segments):
        fail(f"invalid Lean namespace {namespace!r}")
    return segments


def source_key(path: Path) -> str:
    return path.as_posix()


def path_from_segments(segments: Sequence[str]) -> str:
    if not segments or any(not segment for segment in segments):
        fail("empty path segment")
    return "{ segments := " + lean_list([lean_string(segment) for segment in segments]) + " }"


def path_from_name(name: str) -> str:
    return path_from_segments([name])


def path_from_node(node: dict[str, Any]) -> str:
    node_type = node.get("nodeType")
    if node_type == "Identifier":
        name = node.get("name")
        if not isinstance(name, str):
            fail("Identifier path missing name")
        return path_from_name(name)
    if node_type in ("IdentifierPath", "UserDefinedTypeName"):
        name = node.get("name") or node.get("pathNode", {}).get("name")
        if not isinstance(name, str):
            fail(f"{node_type} missing name")
        return path_from_segments(name.split("."))
    if node_type == "MemberAccess":
        expression = node.get("expression")
        member = node.get("memberName")
        if not isinstance(expression, dict) or not isinstance(member, str):
            fail("MemberAccess path missing expression or memberName")
        base = node_path_segments(expression)
        return path_from_segments([*base, member])
    fail(f"unsupported path node {node_type!r}")


def node_path_segments(node: dict[str, Any]) -> list[str]:
    node_type = node.get("nodeType")
    if node_type == "Identifier":
        name = node.get("name")
        if not isinstance(name, str):
            fail("Identifier path missing name")
        return [name]
    if node_type in ("IdentifierPath", "UserDefinedTypeName"):
        name = node.get("name") or node.get("pathNode", {}).get("name")
        if not isinstance(name, str):
            fail(f"{node_type} missing name")
        return name.split(".")
    if node_type == "MemberAccess":
        expression = node.get("expression")
        member = node.get("memberName")
        if not isinstance(expression, dict) or not isinstance(member, str):
            fail("MemberAccess path missing expression or memberName")
        return [*node_path_segments(expression), member]
    fail(f"unsupported path node {node_type!r}")


def iter_node_types(value: Any) -> list[str]:
    found: list[str] = []

    def go(item: Any) -> None:
        if isinstance(item, dict):
            node_type = item.get("nodeType")
            if isinstance(node_type, str):
                found.append(node_type)
            for child in item.values():
                go(child)
        elif isinstance(item, list):
            for child in item:
                go(child)

    go(value)
    return found


def node_type_counts(value: Any) -> dict[str, int]:
    counts: dict[str, int] = {}
    for node_type in iter_node_types(value):
        counts[node_type] = counts.get(node_type, 0) + 1
    return dict(sorted(counts.items()))


def node_type_status(node_type: str) -> str:
    if node_type in SUPPORTED_NODE_TYPES:
        return "supported"
    if node_type in METADATA_NODE_TYPES:
        return "metadata"
    if node_type in EXCLUDED_NODE_TYPES or node_type.startswith("Yul"):
        return "excluded"
    return "unimplemented"


def child_field_key(parent_type: str, field_path: str) -> str:
    return f"{parent_type}.{field_path}"


def child_field_status(parent_type: str, field_path: str) -> str:
    field = (parent_type, field_path)
    if field in SOURCE_CHILD_FIELDS:
        return "source"
    if field in METADATA_CHILD_FIELDS:
        return "metadata"
    return "unclassified"


def scalar_field_status(parent_type: str, field_path: str) -> str:
    field = (parent_type, field_path)
    if field in SOURCE_SCALAR_FIELDS:
        return "source"
    if field in ANALYSIS_SCALAR_FIELDS:
        return "analysis"
    if field in METADATA_SCALAR_FIELDS:
        return "metadata"
    if field_path in METADATA_SCALAR_FIELD_SUFFIXES:
        return "metadata"
    if field_path.startswith("exportedSymbols."):
        return "metadata"
    if field_path.startswith("internalFunctionIDs."):
        return "metadata"
    return "unclassified"


def iter_child_edges(value: Any) -> list[tuple[str, str, str]]:
    edges: list[tuple[str, str, str]] = []

    def collect(parent_type: str, item: Any, field_path: str) -> None:
        if isinstance(item, dict):
            child_type = item.get("nodeType")
            if isinstance(child_type, str):
                edges.append((parent_type, field_path, child_type))
                walk(item)
                return
            for key, child in item.items():
                next_path = f"{field_path}.{key}" if field_path else key
                collect(parent_type, child, next_path)
        elif isinstance(item, list):
            for child in item:
                collect(parent_type, child, field_path)

    def walk(item: Any) -> None:
        if isinstance(item, dict):
            node_type = item.get("nodeType")
            if isinstance(node_type, str):
                for key, child in item.items():
                    if key != "nodeType":
                        collect(node_type, child, key)
                return
            for child in item.values():
                walk(child)
        elif isinstance(item, list):
            for child in item:
                walk(child)

    walk(value)
    return edges


def scalar_value_repr(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def iter_scalar_fields(value: Any) -> list[tuple[str, str, Any]]:
    fields: list[tuple[str, str, Any]] = []

    def is_scalar(item: Any) -> bool:
        return item is None or isinstance(item, (str, int, float, bool))

    def collect(parent_type: str, item: Any, field_path: str) -> None:
        if isinstance(item, dict):
            if isinstance(item.get("nodeType"), str):
                return
            for key, child in item.items():
                next_path = f"{field_path}.{key}" if field_path else key
                collect(parent_type, child, next_path)
        elif isinstance(item, list):
            for child in item:
                if isinstance(child, dict):
                    if isinstance(child.get("nodeType"), str):
                        continue
                    collect(parent_type, child, field_path)
                elif is_scalar(child):
                    fields.append((parent_type, field_path, child))
                else:
                    fields.append((parent_type, field_path, child))
        elif is_scalar(item):
            fields.append((parent_type, field_path, item))
        else:
            fields.append((parent_type, field_path, item))

    def walk(item: Any) -> None:
        if isinstance(item, dict):
            node_type = item.get("nodeType")
            if isinstance(node_type, str):
                for key, child in item.items():
                    if key != "nodeType":
                        collect(node_type, child, key)
                for child in item.values():
                    walk(child)
                return
            for child in item.values():
                walk(child)
        elif isinstance(item, list):
            for child in item:
                walk(child)

    walk(value)
    return fields


def child_field_counts(value: Any) -> dict[str, dict[str, int]]:
    counts: dict[str, dict[str, int]] = {}
    for parent_type, field_path, child_type in iter_child_edges(value):
        key = child_field_key(parent_type, field_path)
        children = counts.setdefault(key, {})
        children[child_type] = children.get(child_type, 0) + 1
    return {key: dict(sorted(children.items())) for key, children in sorted(counts.items())}


def scalar_field_counts(value: Any) -> dict[str, int]:
    counts: dict[str, int] = {}
    for parent_type, field_path, _field_value in iter_scalar_fields(value):
        key = child_field_key(parent_type, field_path)
        counts[key] = counts.get(key, 0) + 1
    return dict(sorted(counts.items()))


def source_scalar_value_counts(value: Any) -> dict[str, dict[str, int]]:
    counts: dict[str, dict[str, int]] = {}
    for parent_type, field_path, field_value in iter_scalar_fields(value):
        field = (parent_type, field_path)
        if field not in SOURCE_SCALAR_VALUE_DOMAINS:
            continue
        key = child_field_key(parent_type, field_path)
        values = counts.setdefault(key, {})
        value_key = scalar_value_repr(field_value)
        values[value_key] = values.get(value_key, 0) + 1
    return {key: dict(sorted(values.items())) for key, values in sorted(counts.items())}


def unknown_source_scalar_value_counts(value: Any) -> dict[str, dict[str, int]]:
    counts: dict[str, dict[str, int]] = {}
    for parent_type, field_path, field_value in iter_scalar_fields(value):
        domain = SOURCE_SCALAR_VALUE_DOMAINS.get((parent_type, field_path))
        if domain is None or field_value in domain:
            continue
        key = child_field_key(parent_type, field_path)
        values = counts.setdefault(key, {})
        value_key = scalar_value_repr(field_value)
        values[value_key] = values.get(value_key, 0) + 1
    return {key: dict(sorted(values.items())) for key, values in sorted(counts.items())}


def child_field_coverage(value: Any) -> dict[str, Any]:
    counts = child_field_counts(value)
    by_status = {
        "source": {},
        "metadata": {},
        "unclassified": {},
    }
    for key, children in counts.items():
        parent_type, _, field_path = key.partition(".")
        by_status[child_field_status(parent_type, field_path)][key] = children
    return {
        "childFields": counts,
        "sourceChildFields": by_status["source"],
        "metadataChildFields": by_status["metadata"],
        "unclassifiedChildFields": by_status["unclassified"],
    }


def scalar_field_coverage(value: Any) -> dict[str, Any]:
    counts = scalar_field_counts(value)
    by_status = {
        "source": {},
        "analysis": {},
        "metadata": {},
        "unclassified": {},
    }
    for key, count in counts.items():
        parent_type, _, field_path = key.partition(".")
        by_status[scalar_field_status(parent_type, field_path)][key] = count
    return {
        "scalarFields": counts,
        "sourceScalarFields": by_status["source"],
        "analysisScalarFields": by_status["analysis"],
        "metadataScalarFields": by_status["metadata"],
        "unclassifiedScalarFields": by_status["unclassified"],
        "sourceScalarValues": source_scalar_value_counts(value),
        "unknownSourceScalarValues": unknown_source_scalar_value_counts(value),
    }


def frontend_coverage(ast: dict[str, Any]) -> dict[str, Any]:
    counts = node_type_counts(ast)
    by_status = {
        "supported": {},
        "metadata": {},
        "excluded": {},
        "unimplemented": {},
    }
    for node_type, count in counts.items():
        by_status[node_type_status(node_type)][node_type] = count
    return {
        "nodeTypes": counts,
        "supported": by_status["supported"],
        "metadata": by_status["metadata"],
        "excluded": by_status["excluded"],
        "unimplemented": by_status["unimplemented"],
        **child_field_coverage(ast),
        **scalar_field_coverage(ast),
    }


def guard_no_unsupported_nodes(ast: dict[str, Any]) -> None:
    coverage = frontend_coverage(ast)
    excluded = coverage["excluded"]
    details = []
    for node_type in sorted(excluded):
        reason = EXCLUDED_NODE_TYPES.get(
            node_type,
            "Yul AST nodes are intentionally out of scope",
        )
        details.append(f"{node_type} ({reason})")
    if details:
        fail("excluded Solidity AST nodes present: " + "; ".join(details))
    unimplemented = coverage["unimplemented"]
    if unimplemented:
        fail("unimplemented Solidity AST nodes present: " + ", ".join(sorted(unimplemented)))
    unclassified_fields = coverage["unclassifiedChildFields"]
    if unclassified_fields:
        fail("unclassified Solidity AST child fields present: " + ", ".join(sorted(unclassified_fields)))
    unclassified_scalars = coverage["unclassifiedScalarFields"]
    if unclassified_scalars:
        fail("unclassified Solidity AST scalar fields present: " + ", ".join(sorted(unclassified_scalars)))
    unknown_scalar_values = coverage["unknownSourceScalarValues"]
    if unknown_scalar_values:
        fail("unknown Solidity AST source scalar values present: " + ", ".join(sorted(unknown_scalar_values)))


def standard_json_input(path: Path) -> dict[str, Any]:
    name = source_key(path)
    return {
        "language": "Solidity",
        "sources": {name: {"content": path.read_text(encoding="utf-8")}},
        "settings": {"outputSelection": {"*": {"": ["ast"]}}},
    }


def run_solc_ast(solc: str, path: Path) -> tuple[str, dict[str, Any]]:
    request = standard_json_input(path)
    completed = subprocess.run(
        [solc, "--standard-json"],
        input=json.dumps(request),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    try:
        output = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        fail(f"solc did not return JSON: {exc}\nstdout was:\n{completed.stdout}")
    diagnostics = output.get("errors", [])
    errors = [
        item.get("formattedMessage") or item.get("message") or str(item)
        for item in diagnostics
        if isinstance(item, dict)
        if item.get("severity") == "error"
    ]
    if completed.returncode != 0 or errors:
        fail("\n".join(errors) or completed.stderr or f"solc exited {completed.returncode}")
    sources = output.get("sources")
    name = source_key(path)
    if not isinstance(sources, dict) or name not in sources:
        fail(f"solc output did not contain source {name!r}")
    ast = sources[name].get("ast")
    if not isinstance(ast, dict):
        fail(f"solc output for {name!r} did not contain an AST")
    return name, ast


def find_contract(ast: dict[str, Any], contract_name: str) -> dict[str, Any]:
    for node in contract_definitions(ast):
        if node.get("name") == contract_name:
            return node
    fail(f"contract {contract_name!r} not found in solc AST")


def contract_definitions(ast: dict[str, Any]) -> list[dict[str, Any]]:
    contracts = []
    for node in ast.get("nodes", []):
        if not isinstance(node, dict):
            continue
        if node.get("nodeType") != "ContractDefinition":
            continue
        contracts.append(node)
    return contracts


def type_from_name(name: str) -> str:
    if name == "bool":
        return "Ty.bool"
    if name == "address":
        return "Ty.address false"
    if name == "address payable":
        return "Ty.address true"
    if name == "string":
        return "Ty.string"
    if name == "bytes":
        return "Ty.bytes"
    match = re.fullmatch("uint([0-9]*)", name)
    if match:
        bits = int(match.group(1) or "256")
        return f"Ty.uint {bits}"
    match = re.fullmatch("int([0-9]*)", name)
    if match:
        bits = int(match.group(1) or "256")
        return f"Ty.int {bits}"
    match = re.fullmatch("bytes([0-9]+)", name)
    if match:
        return f"Ty.bytesN {int(match.group(1))}"
    match = re.fullmatch("fixed([0-9]+)x([0-9]+)", name)
    if match:
        return f"Ty.fixed {int(match.group(1))} {int(match.group(2))}"
    match = re.fullmatch("ufixed([0-9]+)x([0-9]+)", name)
    if match:
        return f"Ty.ufixed {int(match.group(1))} {int(match.group(2))}"
    fail(f"unsupported Solidity elementary type {name!r}")


def unit_denomination(value: str) -> str:
    mapping = {
        "wei": "UnitDenomination.wei",
        "gwei": "UnitDenomination.gwei",
        "ether": "UnitDenomination.ether",
        "seconds": "UnitDenomination.seconds",
        "minutes": "UnitDenomination.minutes",
        "hours": "UnitDenomination.hours",
        "days": "UnitDenomination.days",
        "weeks": "UnitDenomination.weeks",
    }
    if value not in mapping:
        fail(f"unsupported unit denomination {value!r}")
    return mapping[value]


def literal_number_nat(node: dict[str, Any]) -> int:
    if node.get("nodeType") != "Literal" or node.get("kind") != "number":
        fail("expected numeric literal")
    value = node.get("value")
    if not isinstance(value, str) or not re.fullmatch("[0-9]+", value):
        fail("numeric literal must be a decimal natural number")
    return int(value)


def array_length_nat_from_node(node: dict[str, Any]) -> int:
    length = node.get("length")
    if isinstance(length, dict) and length.get("nodeType") == "Literal":
        try:
            return literal_number_nat(length)
        except ImportError:
            pass
    type_descriptions = node.get("typeDescriptions")
    type_string = None
    if isinstance(type_descriptions, dict):
        raw_type_string = type_descriptions.get("typeString")
        if isinstance(raw_type_string, str):
            type_string = raw_type_string
    if type_string is not None:
        match = re.search("\\[([0-9]+)\\]$", type_string)
        if match:
            return int(match.group(1))
    fail("ArrayTypeName length must resolve to a concrete static length")


def type_expression_length_nat_from_node(index: dict[str, Any]) -> int:
    # The index of an array *type expression* (e.g. `uint8[1e1]`) may be a
    # scientific/unit-denominated literal that isn't a bare `[0-9]+`. Mirror the
    # typeString fallback used by `array_length_nat_from_node`: read solc's
    # already-folded value off the index node's typeDescriptions.
    try:
        return literal_number_nat(index)
    except ImportError:
        pass
    type_descriptions = index.get("typeDescriptions")
    if isinstance(type_descriptions, dict):
        raw_type_string = type_descriptions.get("typeString")
        if isinstance(raw_type_string, str):
            match = re.search("int_const ([0-9]+)$", raw_type_string)
            if match:
                return int(match.group(1))
        type_identifier = type_descriptions.get("typeIdentifier")
        if isinstance(type_identifier, str):
            match = re.fullmatch("t_rational_([0-9]+)_by_1", type_identifier)
            if match:
                return int(match.group(1))
    fail("array type expression length must resolve to a concrete static length")


def is_type_expression_node(node: dict[str, Any]) -> bool:
    type_descriptions = node.get("typeDescriptions")
    if not isinstance(type_descriptions, dict):
        return False
    type_identifier = type_descriptions.get("typeIdentifier")
    return isinstance(type_identifier, str) and type_identifier.startswith("t_type$")


def type_from_node(node: dict[str, Any]) -> str:
    node_type = node.get("nodeType")
    if node_type == "ElementaryTypeName":
        name = node.get("name")
        if not isinstance(name, str):
            fail("ElementaryTypeName missing name")
        if name == "address" and node.get("stateMutability") == "payable":
            name = "address payable"
        return type_from_name(name)
    if node_type == "UserDefinedTypeName":
        path = node.get("pathNode", {}).get("name") or node.get("name")
        if not isinstance(path, str):
            fail("UserDefinedTypeName missing name")
        return f"Ty.user ({path_from_segments(path.split('.'))})"
    if node_type == "Mapping":
        key_type = node.get("keyType")
        value_type = node.get("valueType")
        if not isinstance(key_type, dict) or not isinstance(value_type, dict):
            fail("Mapping missing keyType or valueType")
        return f"Ty.mapping ({type_from_node(key_type)}) ({type_from_node(value_type)})"
    if node_type == "ArrayTypeName":
        base_type = node.get("baseType")
        if not isinstance(base_type, dict):
            fail("ArrayTypeName missing baseType")
        length = node.get("length")
        length_part = "none"
        if length is not None:
            if not isinstance(length, dict):
                fail("ArrayTypeName.length must be an object")
            length_value = array_length_nat_from_node(node)
            length_part = f"some {length_value}"
        return f"Ty.array ({type_from_node(base_type)}) ({length_part})"
    if node_type == "FunctionTypeName":
        params = node.get("parameterTypes")
        returns = node.get("returnParameterTypes")
        if not isinstance(params, dict) or not isinstance(returns, dict):
            fail("FunctionTypeName missing parameter or return type list")
        function_visibility = str(node.get("visibility", "internal"))
        return (
            "Ty.functionWithLocations "
            + parameter_type_list(params)
            + " "
            + parameter_location_list(params)
            + " "
            + parameter_type_list(returns)
            + " "
            + parameter_location_list(returns)
            + " "
            + state_mutability(str(node.get("stateMutability", "nonpayable")))
            + " "
            + visibility_value(function_visibility)
        )
    fail(f"unsupported type node {node_type!r}")


def type_from_expression_node(node: dict[str, Any]) -> str:
    node_type = node.get("nodeType")
    if node_type == "ElementaryTypeNameExpression":
        type_name = node.get("typeName")
        if not isinstance(type_name, dict):
            fail("ElementaryTypeNameExpression missing typeName")
        return type_from_node(type_name)
    if node_type == "Identifier":
        name = node.get("name")
        if not isinstance(name, str):
            fail("type Identifier missing name")
        return f"Ty.user ({path_from_name(name)})"
    if node_type == "MemberAccess":
        return f"Ty.user ({path_from_segments(node_path_segments(node))})"
    if node_type == "IndexAccess" and is_type_expression_node(node):
        base = node.get("baseExpression")
        index = node.get("indexExpression")
        if not isinstance(base, dict):
            fail("array type expression missing baseExpression")
        length_part = "none"
        if index is not None:
            if not isinstance(index, dict):
                fail("array type expression index must be an object")
            length_part = f"some {type_expression_length_nat_from_node(index)}"
        return "Ty.array (" + type_from_expression_node(base) + ") (" + length_part + ")"
    fail(f"unsupported type expression node {node_type!r}")


def is_payable_address_type_node(node: Any) -> bool:
    return (
        isinstance(node, dict)
        and node.get("nodeType") == "ElementaryTypeName"
        and node.get("name") == "address"
        and node.get("stateMutability") == "payable"
    )


def parameter_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "VariableDeclaration":
        fail("expected VariableDeclaration parameter")
    type_name = node.get("typeName")
    if not isinstance(type_name, dict):
        fail("parameter missing typeName")
    name = node.get("name")
    name_part = lean_option(lean_string(name)) if isinstance(name, str) and name else "none"
    location = node.get("storageLocation")
    location_part = "none"
    if location == "memory":
        location_part = "some DataLocation.memory"
    elif location == "calldata":
        location_part = "some DataLocation.calldata"
    elif location == "storage":
        location_part = "some DataLocation.storage"
    return (
        "{ name := "
        + name_part
        + ", ty := "
        + type_from_node(type_name)
        + ", location := "
        + location_part
        + " }"
    )


def var_binding_from_node(node: Any) -> str:
    if node is None:
        return "{ name := none, ty := none, location := none }"
    if not isinstance(node, dict):
        fail("unsupported tuple-style variable declaration")
    return parameter_from_node(node)


def parameter_list(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "ParameterList":
        fail("expected ParameterList")
    params = node.get("parameters", [])
    if not isinstance(params, list):
        fail("ParameterList.parameters must be a list")
    return lean_list([parameter_from_node(param) for param in params])


def parameter_type_list(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "ParameterList":
        fail("expected ParameterList")
    params = node.get("parameters", [])
    if not isinstance(params, list):
        fail("ParameterList.parameters must be a list")
    types = []
    for param in params:
        if not isinstance(param, dict) or param.get("nodeType") != "VariableDeclaration":
            fail("function type parameter must be a VariableDeclaration")
        type_name = param.get("typeName")
        if not isinstance(type_name, dict):
            fail("function type parameter missing typeName")
        types.append(type_from_node(type_name))
    return lean_list(types)


def parameter_location_list(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "ParameterList":
        fail("expected ParameterList")
    params = node.get("parameters", [])
    if not isinstance(params, list):
        fail("ParameterList.parameters must be a list")
    locations = []
    for param in params:
        if not isinstance(param, dict) or param.get("nodeType") != "VariableDeclaration":
            fail("function type parameter must be a VariableDeclaration")
        location = param.get("storageLocation")
        if location in (None, "default"):
            locations.append("none")
        elif location == "memory":
            locations.append("some DataLocation.memory")
        elif location == "calldata":
            locations.append("some DataLocation.calldata")
        elif location == "storage":
            locations.append("some DataLocation.storage")
        else:
            fail(f"unsupported function type data location {location!r}")
    return lean_list(locations)


def visibility(value: str) -> str:
    mapping = {
        "public": "some Visibility.public_",
        "private": "some Visibility.private_",
        "internal": "some Visibility.internal_",
        "external": "some Visibility.external_",
        "default": "none",
    }
    if value not in mapping:
        fail(f"unsupported visibility {value!r}")
    return mapping[value]


def visibility_value(value: str) -> str:
    mapping = {
        "public": "Visibility.public_",
        "private": "Visibility.private_",
        "internal": "Visibility.internal_",
        "external": "Visibility.external_",
    }
    if value not in mapping:
        fail(f"unsupported visibility {value!r}")
    return mapping[value]


def state_mutability(value: str) -> str:
    mapping = {
        "pure": "StateMutability.pure",
        "view": "StateMutability.view",
        "nonpayable": "StateMutability.nonpayable",
        "payable": "StateMutability.payable",
    }
    if value not in mapping:
        fail(f"unsupported state mutability {value!r}")
    return mapping[value]


def function_kind(value: str) -> str:
    mapping = {
        "function": "FunctionKind.function",
        "freeFunction": "FunctionKind.function",
        "constructor": "FunctionKind.constructor",
        "receive": "FunctionKind.receive",
        "fallback": "FunctionKind.fallback",
    }
    if value not in mapping:
        fail(f"unsupported function kind {value!r}")
    return mapping[value]


def override_specifier_from_node(node: Any) -> str:
    if node is None:
        return "none"
    if not isinstance(node, dict) or node.get("nodeType") != "OverrideSpecifier":
        fail("override specifier must be an OverrideSpecifier")
    overrides = node.get("overrides", [])
    if not isinstance(overrides, list):
        fail("OverrideSpecifier.overrides must be a list")
    if not all(isinstance(override, dict) for override in overrides):
        fail("OverrideSpecifier.overrides entries must be nodes")
    return "some { bases := " + lean_list([path_from_node(override) for override in overrides]) + " }"


def var_mutability(value: str) -> str:
    mapping = {
        "mutable": "VarMutability.mutable",
        "constant": "VarMutability.constant",
        "immutable": "VarMutability.immutable",
        "transient": "VarMutability.transient",
    }
    if value not in mapping:
        fail(f"unsupported variable mutability {value!r}")
    return mapping[value]


def binary_op(op: str) -> str:
    mapping = {
        "+": "BinaryOp.add",
        "-": "BinaryOp.sub",
        "*": "BinaryOp.mul",
        "/": "BinaryOp.div",
        "%": "BinaryOp.mod",
        "**": "BinaryOp.exp",
        "==": "BinaryOp.eq",
        "!=": "BinaryOp.ne",
        "<": "BinaryOp.lt",
        ">": "BinaryOp.gt",
        "<=": "BinaryOp.le",
        ">=": "BinaryOp.ge",
        "&&": "BinaryOp.boolAnd",
        "||": "BinaryOp.boolOr",
        "&": "BinaryOp.bitAnd",
        "|": "BinaryOp.bitOr",
        "^": "BinaryOp.bitXor",
        "<<": "BinaryOp.shl",
        ">>": "BinaryOp.shr",
    }
    if op not in mapping:
        fail(f"unsupported binary operator {op!r}")
    return mapping[op]


def using_operator(op: str, param_count: int | None = None) -> str:
    binary_mapping = {
        "+": "BinaryOp.add",
        "-": "BinaryOp.sub",
        "*": "BinaryOp.mul",
        "/": "BinaryOp.div",
        "%": "BinaryOp.mod",
        "**": "BinaryOp.exp",
        "==": "BinaryOp.eq",
        "!=": "BinaryOp.ne",
        "<": "BinaryOp.lt",
        ">": "BinaryOp.gt",
        "<=": "BinaryOp.le",
        ">=": "BinaryOp.ge",
        "&": "BinaryOp.bitAnd",
        "|": "BinaryOp.bitOr",
        "^": "BinaryOp.bitXor",
    }
    if op == "~":
        return "some (UsingOperator.unary UnaryOp.bitNot)"
    if op == "-" and param_count == 1:
        return "some (UsingOperator.unary UnaryOp.neg)"
    if op in binary_mapping:
        return f"some (UsingOperator.binary {binary_mapping[op]})"
    fail(f"unsupported using operator {op!r}")


def assign_op(op: str) -> str:
    mapping = {
        "=": "AssignOp.assign",
        "+=": "AssignOp.addAssign",
        "-=": "AssignOp.subAssign",
        "*=": "AssignOp.mulAssign",
        "/=": "AssignOp.divAssign",
        "%=": "AssignOp.modAssign",
        "&=": "AssignOp.bitAndAssign",
        "|=": "AssignOp.bitOrAssign",
        "^=": "AssignOp.bitXorAssign",
        "<<=": "AssignOp.shlAssign",
        ">>=": "AssignOp.shrAssign",
    }
    if op not in mapping:
        fail(f"unsupported assignment operator {op!r}")
    return mapping[op]


def unary_op(op: str, prefix: Any) -> str:
    mapping = {
        "!": "UnaryOp.logicalNot",
        "~": "UnaryOp.bitNot",
        "-": "UnaryOp.neg",
        "delete": "UnaryOp.delete",
    }
    if op == "++":
        if prefix is True:
            return "UnaryOp.preIncrement"
        return "UnaryOp.postIncrement"
    if op == "--":
        if prefix is True:
            return "UnaryOp.preDecrement"
        return "UnaryOp.postDecrement"
    if op not in mapping:
        fail(f"unsupported unary operator {op!r}")
    return mapping[op]


def args_from_nodes(args: list[Any], names: Any = None) -> str:
    if names is None or names == []:
        return lean_list([f"Arg.positional ({expr_from_node(arg)})" for arg in args])
    if not isinstance(names, list):
        fail("FunctionCall.names must be a list when present")
    if len(names) != len(args) or not all(isinstance(name, str) for name in names):
        fail("FunctionCall.names must match arguments")
    return lean_list([
        f"Arg.named {lean_string(name)} ({expr_from_node(arg)})"
        for name, arg in zip(names, args)
    ])


def call_options_from_nodes(options: list[Any], names: Any) -> str:
    if not isinstance(names, list):
        fail("FunctionCallOptions.names must be a list")
    if len(names) != len(options) or not all(isinstance(name, str) for name in names):
        fail("FunctionCallOptions.names must match options")
    return lean_list([
        f"CallOption.named {lean_string(name)} ({expr_from_node(option)})"
        for name, option in zip(names, options)
    ])


def tuple_item_from_node(node: Any) -> str:
    if node is None:
        return "TupleItem.hole"
    if not isinstance(node, dict):
        fail("unsupported tuple expression component")
    return f"TupleItem.value ({expr_from_node(node)})"


def try_clause_params_from_node(node: dict[str, Any]) -> str:
    params = node.get("parameters")
    if params is None:
        return "[]"
    if not isinstance(params, dict):
        fail("TryCatchClause.parameters must be a parameter list")
    return parameter_list(params)


def try_clause_body_from_node(node: dict[str, Any]) -> str:
    block = node.get("block")
    if not isinstance(block, dict):
        fail("TryCatchClause missing block")
    return stmt_from_node(block)


def catch_clause_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "TryCatchClause":
        fail("expected TryCatchClause")
    error_name = node.get("errorName", "")
    if not isinstance(error_name, str):
        fail("TryCatchClause.errorName must be a string")
    name_part = "none" if error_name == "" else f"(some {lean_string(error_name)})"
    return (
        "CatchClause.clause "
        + name_part
        + " "
        + try_clause_params_from_node(node)
        + " ("
        + try_clause_body_from_node(node)
        + ")"
    )


def expr_from_node(node: dict[str, Any]) -> str:
    node_type = node.get("nodeType")
    if node_type == "Identifier":
        name = node.get("name")
        if not isinstance(name, str):
            fail("Identifier missing name")
        if name == "super":
            return f"Expr.ident {lean_string(name)}"
        if is_type_expression_node(node):
            return f"Expr.typeName (Ty.user ({path_from_name(name)}))"
        return f"Expr.ident {lean_string(name)}"
    if node_type == "Literal":
        kind = node.get("kind")
        if kind == "number":
            value = node.get("value")
            if not isinstance(value, str):
                fail("number literal missing value")
            type_descriptions = node.get("typeDescriptions")
            type_identifier = None
            if isinstance(type_descriptions, dict):
                type_identifier = type_descriptions.get("typeIdentifier")
            if type_identifier == "t_address":
                try:
                    address = int(value, 16)
                except ValueError:
                    fail(f"address literal has invalid value {value!r}")
                return f"Expr.literal (Literal.address {address})"
            subdenomination = node.get("subdenomination")
            if isinstance(subdenomination, str) and subdenomination:
                return (
                    "Expr.literal (Literal.unitNumber "
                    + lean_string(value)
                    + " "
                    + unit_denomination(subdenomination)
                    + ")"
                )
            return f"Expr.literal (Literal.number {lean_string(value)})"
        if kind == "bool":
            value = node.get("value")
            if value not in ("true", "false"):
                fail("bool literal has unexpected value")
            return f"Expr.literal (Literal.bool {'true' if value == 'true' else 'false'})"
        if kind == "string":
            value = node.get("value")
            if not isinstance(value, str):
                fail("string literal missing value")
            return f"Expr.literal (Literal.string {lean_string(value)})"
        if kind == "hexString":
            value = node.get("hexValue")
            if not isinstance(value, str):
                fail("hex string literal missing hexValue")
            return f"Expr.literal (Literal.hexString {lean_string(value)})"
        if kind == "unicodeString":
            value = node.get("value")
            if not isinstance(value, str):
                fail("unicode string literal missing value")
            return f"Expr.literal (Literal.unicodeString {lean_string(value)})"
        fail(f"unsupported literal kind {kind!r}")
    if node_type == "ElementaryTypeNameExpression":
        type_name = node.get("typeName")
        if not isinstance(type_name, dict):
            fail("ElementaryTypeNameExpression missing typeName")
        return f"Expr.typeName ({type_from_node(type_name)})"
    if node_type == "TupleExpression":
        components = node.get("components", [])
        if not isinstance(components, list):
            fail("TupleExpression.components must be a list")
        if node.get("isInlineArray") is True:
            if any(component is None for component in components):
                fail("inline array expression cannot contain tuple holes")
            return "Expr.array " + lean_list([expr_from_node(component) for component in components])
        if len(components) == 1 and isinstance(components[0], dict):
            return expr_from_node(components[0])
        return "Expr.tuple " + lean_list([tuple_item_from_node(component) for component in components])
    if node_type == "UnaryOperation":
        sub_expression = node.get("subExpression")
        op = node.get("operator")
        if not isinstance(sub_expression, dict) or not isinstance(op, str):
            fail("UnaryOperation missing subExpression or operator")
        return (
            "Expr.unary "
            + unary_op(op, node.get("prefix"))
            + " ("
            + expr_from_node(sub_expression)
            + ")"
        )
    if node_type == "FunctionCall":
        expression = node.get("expression")
        args = node.get("arguments", [])
        if not isinstance(expression, dict) or not isinstance(args, list):
            fail("FunctionCall missing expression or arguments")
        if (
            node.get("kind") == "typeConversion"
            and expression.get("nodeType") == "ElementaryTypeNameExpression"
            and is_payable_address_type_node(expression.get("typeName"))
        ):
            if len(args) != 1:
                fail("payable(...) conversion must have one argument")
            if node.get("names") not in (None, []):
                fail("payable(...) conversion cannot have named arguments")
            return "Expr.payableConversion (" + expr_from_node(args[0]) + ")"
        if expression.get("nodeType") == "FunctionCallOptions":
            option_target = expression.get("expression")
            options = expression.get("options", [])
            if not isinstance(option_target, dict) or not isinstance(options, list):
                fail("FunctionCallOptions missing expression or options")
            if option_target.get("nodeType") == "NewExpression":
                type_name = option_target.get("typeName")
                if not isinstance(type_name, dict):
                    fail("NewExpression missing typeName")
                target = f"Expr.newExpr ({type_from_node(type_name)}) []"
            else:
                target = expr_from_node(option_target)
            return (
                "Expr.callWithOptions ("
                + target
                + ") "
                + call_options_from_nodes(options, expression.get("names"))
                + " "
                + args_from_nodes(args, node.get("names"))
            )
        if expression.get("nodeType") == "NewExpression":
            type_name = expression.get("typeName")
            if not isinstance(type_name, dict):
                fail("NewExpression missing typeName")
            return (
                "Expr.newExpr ("
                + type_from_node(type_name)
                + ") "
                + args_from_nodes(args, node.get("names"))
            )
        if expression.get("nodeType") == "Identifier" and expression.get("name") == "type":
            if len(args) != 1:
                fail("type(...) call must have one argument")
            return expr_from_node(args[0])
        return "Expr.call (" + expr_from_node(expression) + ") " + args_from_nodes(args, node.get("names"))
    if node_type == "MemberAccess":
        expression = node.get("expression")
        member = node.get("memberName")
        if not isinstance(expression, dict) or not isinstance(member, str):
            fail("MemberAccess missing expression or memberName")
        return f"Expr.member ({expr_from_node(expression)}) {lean_string(member)}"
    if node_type == "IndexAccess":
        base = node.get("baseExpression")
        index = node.get("indexExpression")
        if is_type_expression_node(node):
            return "Expr.typeName (" + type_from_expression_node(node) + ")"
        if not isinstance(base, dict) or not isinstance(index, dict):
            fail("IndexAccess missing baseExpression or indexExpression")
        return f"Expr.index ({expr_from_node(base)}) ({expr_from_node(index)})"
    if node_type == "IndexRangeAccess":
        base = node.get("baseExpression")
        start = node.get("startExpression")
        end = node.get("endExpression")
        if not isinstance(base, dict):
            fail("IndexRangeAccess missing baseExpression")
        if start is not None and not isinstance(start, dict):
            fail("IndexRangeAccess.startExpression must be an object")
        if end is not None and not isinstance(end, dict):
            fail("IndexRangeAccess.endExpression must be an object")
        start_part = "none" if start is None else f"(some ({expr_from_node(start)}))"
        end_part = "none" if end is None else f"(some ({expr_from_node(end)}))"
        return "Expr.slice (" + expr_from_node(base) + ") " + start_part + " " + end_part
    if node_type == "BinaryOperation":
        left = node.get("leftExpression")
        right = node.get("rightExpression")
        op = node.get("operator")
        if not isinstance(left, dict) or not isinstance(right, dict) or not isinstance(op, str):
            fail("BinaryOperation missing left/right/operator")
        return (
            "Expr.binary "
            + binary_op(op)
            + " ("
            + expr_from_node(left)
            + ") ("
            + expr_from_node(right)
            + ")"
        )
    if node_type == "Conditional":
        condition = node.get("condition")
        true_expr = node.get("trueExpression")
        false_expr = node.get("falseExpression")
        if not isinstance(condition, dict) or not isinstance(true_expr, dict) or not isinstance(false_expr, dict):
            fail("Conditional missing condition/trueExpression/falseExpression")
        return (
            "Expr.ternary ("
            + expr_from_node(condition)
            + ") ("
            + expr_from_node(true_expr)
            + ") ("
            + expr_from_node(false_expr)
            + ")"
        )
    if node_type == "Assignment":
        left = node.get("leftHandSide")
        right = node.get("rightHandSide")
        op = node.get("operator")
        if not isinstance(left, dict) or not isinstance(right, dict) or not isinstance(op, str):
            fail("Assignment missing left/right/operator")
        return (
            "Expr.assign ("
            + expr_from_node(left)
            + ") "
            + assign_op(op)
            + " ("
            + expr_from_node(right)
            + ")"
        )
    fail(f"unsupported expression node {node_type!r}")


def stmt_from_node(node: dict[str, Any]) -> str:
    node_type = node.get("nodeType")
    if node_type == "Block":
        statements = node.get("statements", [])
        if not isinstance(statements, list):
            fail("Block.statements must be a list")
        return f"Stmt.block {lean_list([stmt_from_node(stmt) for stmt in statements])}"
    if node_type == "Return":
        expression = node.get("expression")
        if expression is None:
            return "Stmt.returnValues none"
        if not isinstance(expression, dict):
            fail("Return.expression must be an object")
        return f"Stmt.returnValues (some ({expr_from_node(expression)}))"
    if node_type == "ExpressionStatement":
        expression = node.get("expression")
        if not isinstance(expression, dict):
            fail("ExpressionStatement missing expression")
        return f"Stmt.expr ({expr_from_node(expression)})"
    if node_type == "VariableDeclarationStatement":
        declarations = node.get("declarations", [])
        if not isinstance(declarations, list):
            fail("VariableDeclarationStatement.declarations must be a list")
        bindings = [var_binding_from_node(declaration) for declaration in declarations]
        initial = node.get("initialValue")
        init_part = "none"
        if initial is not None:
            if not isinstance(initial, dict):
                fail("VariableDeclarationStatement.initialValue must be an object")
            init_part = f"(some ({expr_from_node(initial)}))"
        return f"Stmt.varDecl {lean_list(bindings)} {init_part}"
    if node_type == "IfStatement":
        condition = node.get("condition")
        true_body = node.get("trueBody")
        false_body = node.get("falseBody")
        if not isinstance(condition, dict) or not isinstance(true_body, dict):
            fail("IfStatement missing condition or trueBody")
        false_part = "none"
        if false_body is not None:
            if not isinstance(false_body, dict):
                fail("IfStatement.falseBody must be an object")
            false_part = f"(some ({stmt_from_node(false_body)}))"
        return "Stmt.ifElse (" + expr_from_node(condition) + ") (" + stmt_from_node(true_body) + ") " + false_part
    if node_type == "WhileStatement":
        condition = node.get("condition")
        body = node.get("body")
        if not isinstance(condition, dict) or not isinstance(body, dict):
            fail("WhileStatement missing condition or body")
        return "Stmt.whileLoop (" + expr_from_node(condition) + ") (" + stmt_from_node(body) + ")"
    if node_type == "DoWhileStatement":
        condition = node.get("condition")
        body = node.get("body")
        if not isinstance(condition, dict) or not isinstance(body, dict):
            fail("DoWhileStatement missing condition or body")
        return "Stmt.doWhile (" + stmt_from_node(body) + ") (" + expr_from_node(condition) + ")"
    if node_type == "ForStatement":
        body = node.get("body")
        if not isinstance(body, dict):
            fail("ForStatement missing body")
        init = node.get("initializationExpression")
        condition = node.get("condition")
        loop_expression = node.get("loopExpression")
        init_part = "none"
        if init is not None:
            if not isinstance(init, dict):
                fail("ForStatement.initializationExpression must be an object")
            init_part = f"(some ({stmt_from_node(init)}))"
        cond_part = "none"
        if condition is not None:
            if not isinstance(condition, dict):
                fail("ForStatement.condition must be an object")
            cond_part = f"(some ({expr_from_node(condition)}))"
        post_part = "none"
        if loop_expression is not None:
            if not isinstance(loop_expression, dict):
                fail("ForStatement.loopExpression must be an object")
            post_expr = loop_expression
            if loop_expression.get("nodeType") == "ExpressionStatement":
                expression = loop_expression.get("expression")
                if not isinstance(expression, dict):
                    fail("ForStatement.loopExpression missing expression")
                post_expr = expression
            post_part = f"(some ({expr_from_node(post_expr)}))"
        return (
            "Stmt.forLoop "
            + init_part
            + " "
            + cond_part
            + " "
            + post_part
            + " ("
            + stmt_from_node(body)
            + ")"
        )
    if node_type == "TryStatement":
        external_call = node.get("externalCall")
        clauses = node.get("clauses", [])
        if not isinstance(external_call, dict):
            fail("TryStatement missing externalCall")
        if not isinstance(clauses, list) or not clauses:
            fail("TryStatement requires a success clause")
        success = clauses[0]
        if not isinstance(success, dict) or success.get("nodeType") != "TryCatchClause":
            fail("TryStatement success clause must be a TryCatchClause")
        if success.get("errorName", "") != "":
            fail("TryStatement success clause must not have an error name")
        catch_clauses = clauses[1:]
        if not all(
            isinstance(clause, dict) and clause.get("nodeType") == "TryCatchClause"
            for clause in catch_clauses
        ):
            fail("TryStatement catch clauses must be TryCatchClause nodes")
        return (
            "Stmt.tryCatchReturns ("
            + expr_from_node(external_call)
            + ") "
            + try_clause_params_from_node(success)
            + " ("
            + try_clause_body_from_node(success)
            + ") "
            + lean_list([catch_clause_from_node(clause) for clause in catch_clauses])
        )
    if node_type == "UncheckedBlock":
        statements = node.get("statements", [])
        if not isinstance(statements, list):
            fail("UncheckedBlock.statements must be a list")
        return f"Stmt.unchecked (Stmt.block {lean_list([stmt_from_node(stmt) for stmt in statements])})"
    if node_type == "EmitStatement":
        event_call = node.get("eventCall")
        if not isinstance(event_call, dict):
            fail("EmitStatement missing eventCall")
        return f"Stmt.emitEvent ({expr_from_node(event_call)})"
    if node_type == "RevertStatement":
        error_call = node.get("errorCall")
        if not isinstance(error_call, dict):
            fail("RevertStatement missing errorCall")
        return f"Stmt.revertCall ({expr_from_node(error_call)})"
    if node_type == "Break":
        return "Stmt.break"
    if node_type == "Continue":
        return "Stmt.continue"
    if node_type == "PlaceholderStatement":
        return "Stmt.modifierPlaceholder"
    fail(f"unsupported statement node {node_type!r}")


def modifier_invocation_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "ModifierInvocation":
        fail("expected ModifierInvocation")
    modifier_name = node.get("modifierName")
    args = node.get("arguments", [])
    if not isinstance(modifier_name, dict):
        fail("ModifierInvocation missing modifierName")
    if args is None:
        args = []
    if not isinstance(args, list):
        fail("ModifierInvocation.arguments must be a list")
    return (
        "{ target := "
        + path_from_node(modifier_name)
        + ", args := "
        + args_from_nodes(args, node.get("names"))
        + " }"
    )


def function_decl_from_node(node: dict[str, Any], force_visibility_none: bool = False) -> str:
    if node.get("nodeType") != "FunctionDefinition":
        fail("expected FunctionDefinition")
    kind = str(node.get("kind", "function"))
    kind_part = function_kind(kind)
    name = node.get("name")
    if kind in ("constructor", "receive", "fallback"):
        name_part = "none"
        name_for_errors = kind
    else:
        if not isinstance(name, str):
            fail("FunctionDefinition missing name")
        name_part = "some " + lean_string(name)
        name_for_errors = name
    params = node.get("parameters")
    returns = node.get("returnParameters")
    body = node.get("body")
    if not isinstance(params, dict) or not isinstance(returns, dict):
        fail(f"function {name_for_errors} missing parameter lists")
    modifiers = node.get("modifiers", [])
    if not isinstance(modifiers, list):
        fail(f"function {name_for_errors} modifiers must be a list")
    body_part = "none"
    if body is not None:
        if not isinstance(body, dict):
            fail(f"function {name_for_errors} body must be an object")
        body_part = f"some ({stmt_from_node(body)})"
    visibility_part = "none" if force_visibility_none else visibility(str(node.get("visibility", "default")))
    return (
        "{ kind := "
        + kind_part
        + ",\n"
        + "    name := "
        + name_part
        + ",\n"
        + "    visibility := "
        + visibility_part
        + ",\n"
        + "    mutability := "
        + state_mutability(str(node.get("stateMutability", "nonpayable")))
        + ",\n"
        + "    params := "
        + parameter_list(params)
        + ",\n"
        + "    returns := "
        + parameter_list(returns)
        + ",\n"
        + "    virtual := "
        + ("true" if node.get("virtual") else "false")
        + ",\n"
        + "    override? := "
        + override_specifier_from_node(node.get("overrides"))
        + ",\n"
        + "    modifiers := "
        + lean_list([modifier_invocation_from_node(modifier) for modifier in modifiers])
        + ",\n"
        + "    body := "
        + body_part
        + " }"
    )


def function_from_node(node: dict[str, Any]) -> str | None:
    if node.get("nodeType") != "FunctionDefinition":
        return None
    return "(ContractItem.function\n  " + function_decl_from_node(node) + ")"


def modifier_from_node(node: dict[str, Any]) -> str | None:
    if node.get("nodeType") != "ModifierDefinition":
        return None
    name = node.get("name")
    params = node.get("parameters")
    body = node.get("body")
    if not isinstance(name, str) or not isinstance(params, dict):
        fail("ModifierDefinition missing name or parameters")
    body_part = "none"
    if body is not None:
        if not isinstance(body, dict):
            fail("ModifierDefinition body must be an object")
        body_part = f"some ({stmt_from_node(body)})"
    return (
        "ContractItem.modifierDecl\n  { name := "
        + lean_string(name)
        + "\n"
        + "    params := "
        + parameter_list(params)
        + "\n"
        + "    virtual := "
        + ("true" if node.get("virtual") else "false")
        + "\n"
        + "    override? := "
        + override_specifier_from_node(node.get("overrides"))
        + "\n"
        + "    body := "
        + body_part
        + " }"
    )


def state_var_decl_from_variable_node(node: dict[str, Any], initial: Any = None, force_visibility_none: bool = False) -> str:
    if node.get("nodeType") != "VariableDeclaration":
        fail("expected VariableDeclaration")
    name = node.get("name")
    type_name = node.get("typeName")
    if not isinstance(name, str) or not name or not isinstance(type_name, dict):
        fail("variable declaration missing name or typeName")
    if initial is None:
        initial = node.get("value") or node.get("initialValue")
    init_part = "none"
    if initial is not None:
        if not isinstance(initial, dict):
            fail("variable initializer must be an object")
        init_part = f"some ({expr_from_node(initial)})"
    visibility_part = "none" if force_visibility_none else visibility(str(node.get("visibility", "default")))
    mutability = str(node.get("mutability", "mutable"))
    if mutability == "mutable" and node.get("storageLocation") == "transient":
        mutability = "transient"
    return (
        "{ name := "
        + lean_string(name)
        + ",\n"
        + "    ty := "
        + type_from_node(type_name)
        + ",\n"
        + "    visibility := "
        + visibility_part
        + ",\n"
        + "    mutability := "
        + var_mutability(mutability)
        + ",\n"
        + "    override? := "
        + override_specifier_from_node(node.get("overrides"))
        + ",\n"
        + "    init := "
        + init_part
        + " }"
    )


def state_var_from_node(node: dict[str, Any]) -> list[str]:
    if node.get("nodeType") == "VariableDeclaration" and node.get("stateVariable") is True:
        return ["(ContractItem.stateVar\n  " + state_var_decl_from_variable_node(node) + ")"]
    if node.get("nodeType") != "StateVariableDeclaration":
        return []
    declarations = node.get("declarations", [])
    if not isinstance(declarations, list):
        fail("StateVariableDeclaration.declarations must be a list")
    initial = node.get("initialValue")
    init_part = "none"
    if initial is not None:
        if not isinstance(initial, dict):
            fail("state variable initialValue must be an object")
        init_part = f"some ({expr_from_node(initial)})"
    rendered = []
    for decl in declarations:
        if not isinstance(decl, dict) or decl.get("nodeType") != "VariableDeclaration":
            fail("state variable declaration must contain VariableDeclaration nodes")
        rendered.append(
            "(ContractItem.stateVar\n  "
            + state_var_decl_from_variable_node(decl, initial)
            + ")"
        )
    return rendered


def event_param_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "VariableDeclaration":
        fail("event parameter must be a VariableDeclaration")
    type_name = node.get("typeName")
    if not isinstance(type_name, dict):
        fail("event parameter missing typeName")
    name = node.get("name")
    name_part = lean_option(lean_string(name)) if isinstance(name, str) and name else "none"
    indexed = "true" if node.get("indexed") is True else "false"
    return (
        "{ name := "
        + name_part
        + ", ty := "
        + type_from_node(type_name)
        + ", indexed := "
        + indexed
        + " }"
    )


def event_from_node(node: dict[str, Any]) -> str | None:
    if node.get("nodeType") != "EventDefinition":
        return None
    return "(ContractItem.eventDecl\n  " + event_decl_from_node(node) + ")"


def event_decl_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "EventDefinition":
        fail("expected EventDefinition")
    name = node.get("name")
    params = node.get("parameters")
    if not isinstance(name, str) or not isinstance(params, dict):
        fail("EventDefinition missing name or parameters")
    param_nodes = params.get("parameters", [])
    if not isinstance(param_nodes, list):
        fail("EventDefinition.parameters.parameters must be a list")
    return (
        "{ name := "
        + lean_string(name)
        + ",\n"
        + "    params := "
        + lean_list([event_param_from_node(param) for param in param_nodes])
        + ",\n"
        + "    anonymous := "
        + ("true" if node.get("anonymous") else "false")
        + " }"
    )


def error_from_node(node: dict[str, Any]) -> str | None:
    if node.get("nodeType") != "ErrorDefinition":
        return None
    return "(ContractItem.errorDecl\n  " + error_decl_from_node(node) + ")"


def error_decl_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "ErrorDefinition":
        fail("expected ErrorDefinition")
    name = node.get("name")
    params = node.get("parameters")
    if not isinstance(name, str) or not isinstance(params, dict):
        fail("ErrorDefinition missing name or parameters")
    param_nodes = params.get("parameters", [])
    if not isinstance(param_nodes, list):
        fail("ErrorDefinition.parameters.parameters must be a list")
    return (
        "{ name := "
        + lean_string(name)
        + ",\n"
        + "    params := "
        + lean_list([parameter_from_node(param) for param in param_nodes])
        + " }"
    )


def base_specifier_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "InheritanceSpecifier":
        fail("base contract entry must be an InheritanceSpecifier")
    base_name = node.get("baseName")
    args = node.get("arguments", [])
    if not isinstance(base_name, dict):
        fail("InheritanceSpecifier missing baseName")
    if args is None:
        args = []
    if not isinstance(args, list):
        fail("InheritanceSpecifier.arguments must be a list")
    return "{ base := " + path_from_node(base_name) + ", args := " + args_from_nodes(args) + " }"


def struct_field_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "VariableDeclaration":
        fail("struct field must be a VariableDeclaration")
    name = node.get("name")
    type_name = node.get("typeName")
    if not isinstance(name, str) or not name or not isinstance(type_name, dict):
        fail("struct field missing name or typeName")
    return "{ name := " + lean_string(name) + ", ty := " + type_from_node(type_name) + " }"


def struct_decl_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "StructDefinition":
        fail("expected StructDefinition")
    name = node.get("name")
    members = node.get("members", [])
    if not isinstance(name, str) or not isinstance(members, list):
        fail("StructDefinition missing name or members")
    return (
        "{ name := "
        + lean_string(name)
        + ",\n"
        + "    fields := "
        + lean_list([struct_field_from_node(member) for member in members])
        + " }"
    )


def struct_from_node(node: dict[str, Any]) -> str | None:
    if node.get("nodeType") != "StructDefinition":
        return None
    return "(ContractItem.structDecl\n  " + struct_decl_from_node(node) + ")"


def enum_decl_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "EnumDefinition":
        fail("expected EnumDefinition")
    name = node.get("name")
    members = node.get("members", [])
    if not isinstance(name, str) or not isinstance(members, list):
        fail("EnumDefinition missing name or members")
    cases = []
    for member in members:
        if not isinstance(member, dict) or member.get("nodeType") != "EnumValue":
            fail("EnumDefinition members must be EnumValue nodes")
        member_name = member.get("name")
        if not isinstance(member_name, str):
            fail("EnumValue missing name")
        cases.append(lean_string(member_name))
    return "{ name := " + lean_string(name) + ",\n" + "    cases := " + lean_list(cases) + " }"


def enum_from_node(node: dict[str, Any]) -> str | None:
    if node.get("nodeType") != "EnumDefinition":
        return None
    return "(ContractItem.enumDecl\n  " + enum_decl_from_node(node) + ")"


def user_value_type_decl_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "UserDefinedValueTypeDefinition":
        fail("expected UserDefinedValueTypeDefinition")
    name = node.get("name")
    underlying = node.get("underlyingType")
    if not isinstance(name, str) or not isinstance(underlying, dict):
        fail("UserDefinedValueTypeDefinition missing name or underlyingType")
    return (
        "{ name := "
        + lean_string(name)
        + ",\n"
        + "    underlying := "
        + type_from_node(underlying)
        + " }"
    )


def user_value_type_from_node(node: dict[str, Any]) -> str | None:
    if node.get("nodeType") != "UserDefinedValueTypeDefinition":
        return None
    return "(ContractItem.userValueTypeDecl\n  " + user_value_type_decl_from_node(node) + ")"


def using_function_from_node(node: dict[str, Any]) -> str:
    definition = node.get("definition") or node.get("function")
    if not isinstance(definition, dict):
        fail("UsingForDirective function entry missing definition/function")
    operator = node.get("operator")
    operator_part = "none"
    if isinstance(operator, str) and operator:
        ref_id = definition.get("referencedDeclaration")
        param_count = FUNCTION_PARAM_COUNT_BY_ID.get(ref_id)
        operator_part = using_operator(operator, param_count)
    return (
        "{ function := "
        + path_from_node(definition)
        + ", operator? := "
        + operator_part
        + " }"
    )


def function_param_count_from_node(node: dict[str, Any]) -> int | None:
    if node.get("nodeType") != "FunctionDefinition":
        return None
    params = node.get("parameters")
    if not isinstance(params, dict):
        return None
    entries = params.get("parameters")
    if not isinstance(entries, list):
        return None
    return len(entries)


def collect_function_param_counts(ast: dict[str, Any]) -> dict[int, int]:
    counts: dict[int, int] = {}

    def visit(node: Any) -> None:
        if isinstance(node, dict):
            node_id = node.get("id")
            param_count = function_param_count_from_node(node)
            if isinstance(node_id, int) and param_count is not None:
                counts[node_id] = param_count
            for value in node.values():
                visit(value)
        elif isinstance(node, list):
            for value in node:
                visit(value)

    visit(ast)
    return counts


def using_decl_from_node(node: dict[str, Any]) -> str:
    if node.get("nodeType") != "UsingForDirective":
        fail("expected UsingForDirective")
    library_name = node.get("libraryName")
    function_list = node.get("functionList")
    if isinstance(library_name, dict):
        library_part = path_from_node(library_name)
        functions_part = "[]"
    elif isinstance(function_list, list):
        library_part = "{ segments := [] }"
        functions_part = lean_list([using_function_from_node(item) for item in function_list])
    else:
        fail("UsingForDirective missing libraryName or functionList")
    type_name = node.get("typeName")
    target_part = "none"
    if type_name is not None:
        if not isinstance(type_name, dict):
            fail("UsingForDirective.typeName must be an object")
        target_part = "some (" + type_from_node(type_name) + ")"
    return (
        "{ library := "
        + library_part
        + ",\n"
        + "    functions := "
        + functions_part
        + ",\n"
        + "    target := "
        + target_part
        + ",\n"
        + "    global := "
        + ("true" if node.get("global") else "false")
        + " }"
    )


def using_from_node(node: dict[str, Any]) -> str | None:
    if node.get("nodeType") != "UsingForDirective":
        return None
    return "(ContractItem.usingDecl\n  " + using_decl_from_node(node) + ")"


def pragma_from_node(node: dict[str, Any]) -> str | None:
    if node.get("nodeType") != "PragmaDirective":
        return None
    literals = node.get("literals", [])
    if not isinstance(literals, list) or not literals:
        fail("PragmaDirective missing literals")
    if not all(isinstance(part, str) for part in literals):
        fail("PragmaDirective literals must be strings")
    name = literals[0]
    value = "".join(literals[1:])
    return "SourceItem.pragma " + lean_string(name) + " " + lean_string(value)


def contract_kind(value: str) -> str:
    mapping = {
        "contract": "ContractKind.contract",
        "interface": "ContractKind.interface",
        "library": "ContractKind.library",
    }
    if value not in mapping:
        fail(f"unsupported contract kind {value!r}")
    return mapping[value]


def render_contract(contract: dict[str, Any]) -> str:
    name = contract.get("name")
    if not isinstance(name, str):
        fail("ContractDefinition missing name")
    nodes = contract.get("nodes", [])
    if not isinstance(nodes, list):
        fail("ContractDefinition.nodes must be a list")
    base_contracts = contract.get("baseContracts", [])
    if not isinstance(base_contracts, list):
        fail("ContractDefinition.baseContracts must be a list")
    items = []
    for node in nodes:
        if not isinstance(node, dict):
            continue
        node_type = node.get("nodeType")
        handled = False
        if node_type in ("StateVariableDeclaration", "VariableDeclaration"):
            handled = True
        items.extend(state_var_from_node(node))
        rendered_event = event_from_node(node)
        if rendered_event is not None:
            handled = True
            items.append(rendered_event)
        rendered_error = error_from_node(node)
        if rendered_error is not None:
            handled = True
            items.append(rendered_error)
        rendered_struct = struct_from_node(node)
        if rendered_struct is not None:
            handled = True
            items.append(rendered_struct)
        rendered_enum = enum_from_node(node)
        if rendered_enum is not None:
            handled = True
            items.append(rendered_enum)
        rendered_user_value_type = user_value_type_from_node(node)
        if rendered_user_value_type is not None:
            handled = True
            items.append(rendered_user_value_type)
        rendered_using = using_from_node(node)
        if rendered_using is not None:
            handled = True
            items.append(rendered_using)
        rendered_modifier = modifier_from_node(node)
        if rendered_modifier is not None:
            handled = True
            items.append(rendered_modifier)
        rendered = function_from_node(node)
        if rendered is not None:
            handled = True
            items.append(rendered)
        if handled:
            continue
        fail(f"unsupported ContractDefinition child node {node_type!r}")
    return (
        "{ kind := "
        + contract_kind(str(contract.get("contractKind", "contract")))
        + "\n"
        + "  name := "
        + lean_string(name)
        + "\n"
        + "  abstract := "
        + ("true" if contract.get("abstract") else "false")
        + "\n"
        + "  bases := "
        + lean_list([base_specifier_from_node(base) for base in base_contracts])
        + "\n"
        + "  items := "
        + lean_list(items)
        + " }"
    )


def source_item_from_node(node: dict[str, Any], contract_def_names: dict[int, str]) -> str | None:
    node_type = node.get("nodeType")
    rendered_pragma = pragma_from_node(node)
    if rendered_pragma is not None:
        return rendered_pragma
    if node_type == "ContractDefinition":
        identity = id(node)
        if identity not in contract_def_names:
            fail("ContractDefinition missing rendered definition")
        return "SourceItem.contract " + contract_def_names[identity]
    if node_type == "FunctionDefinition":
        return "SourceItem.freeFunction\n  " + function_decl_from_node(node, force_visibility_none=True)
    if node_type == "VariableDeclaration":
        if node.get("constant") is True or node.get("mutability") == "constant":
            return "SourceItem.freeConstant\n  " + state_var_decl_from_variable_node(node, force_visibility_none=True)
        fail("unsupported non-constant free variable declaration")
    if node_type == "EventDefinition":
        return "SourceItem.freeEvent\n  " + event_decl_from_node(node)
    if node_type == "ErrorDefinition":
        return "SourceItem.freeError\n  " + error_decl_from_node(node)
    if node_type == "StructDefinition":
        return "SourceItem.freeStruct\n  " + struct_decl_from_node(node)
    if node_type == "EnumDefinition":
        return "SourceItem.freeEnum\n  " + enum_decl_from_node(node)
    if node_type == "UserDefinedValueTypeDefinition":
        return "SourceItem.freeUserValueType\n  " + user_value_type_decl_from_node(node)
    if node_type == "UsingForDirective":
        return "SourceItem.usingDecl\n  " + using_decl_from_node(node)
    return None


def render_module(ast: dict[str, Any], source_name: str, contract_name: str, namespace: str, body_only: bool) -> str:
    global FUNCTION_PARAM_COUNT_BY_ID
    FUNCTION_PARAM_COUNT_BY_ID = collect_function_param_counts(ast)
    guard_no_unsupported_nodes(ast)
    contract = find_contract(ast, contract_name)
    contracts = contract_definitions(ast)
    segments = namespace_segments(namespace)
    lines = []
    if not body_only:
        lines.append("import SolidCore.Solidity.Checked")
        lines.append("import SolidCore.Witness.Checked")
        lines.append("")
    for segment in segments:
        lines.append(f"namespace {segment}")
    lines.append("")
    lines.append(f"def importedSourceName : String := {lean_string(source_name)}")
    lines.append("")
    contract_defs = []
    contract_def_names = {}
    selected_def = ""
    for index, item in enumerate(contracts):
        def_name = f"importedContractDecl{index}"
        contract_defs.append((def_name, item))
        contract_def_names[id(item)] = def_name
        if item is contract:
            selected_def = def_name
        lines.append(f"def {def_name} : ContractDecl :=")
        lines.append(render_contract(item))
        lines.append("")
    if not selected_def:
        fail(f"contract {contract_name!r} not found in contract definition list")
    lines.append("def importedContract : ContractDecl :=")
    lines.append("  " + selected_def)
    lines.append("")
    lines.append("def importedContracts : List ContractDecl :=")
    lines.append("  " + lean_list([def_name for def_name, _ in contract_defs]))
    lines.append("")
    ast_nodes = ast.get("nodes", [])
    if not isinstance(ast_nodes, list):
        fail("SourceUnit.nodes must be a list")
    source_items = []
    for node in ast_nodes:
        if not isinstance(node, dict):
            continue
        rendered = source_item_from_node(node, contract_def_names)
        if rendered is not None:
            source_items.append(rendered)
            continue
        fail(f"unsupported SourceUnit child node {node.get('nodeType')!r}")
    lines.append("def importedSourceUnit : SourceUnit :=")
    lines.append("  { items := " + lean_list(source_items) + " }")
    lines.append("")
    lines.append("def importedContractAccepted : Bool :=")
    lines.append("  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)")
    lines.append("")
    for segment in reversed(segments):
        lines.append(f"end {segment}")
    lines.append("")
    return "\n".join(lines)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--contract")
    parser.add_argument("--solc", default="solc")
    parser.add_argument(
        "--namespace",
        default="SolidCore.Solidity.SolcAstImport.Generated",
    )
    parser.add_argument("--body-only", action="store_true")
    parser.add_argument(
        "--audit-coverage",
        action="store_true",
        help="print JSON coverage for solc AST node kinds and child fields instead of Lean",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        solc = resolve_executable(args.solc)
        source = args.source.resolve()
        source_name, ast = run_solc_ast(solc, source)
        if args.audit_coverage:
            print(json.dumps(frontend_coverage(ast), indent=2, sort_keys=True))
            return 0
        if not isinstance(args.contract, str):
            fail("--contract is required unless --audit-coverage is used")
        print(
            render_module(
                ast,
                source_name,
                args.contract,
                args.namespace,
                args.body_only,
            ),
            end="",
        )
        return 0
    except ImportError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
