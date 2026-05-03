#!/usr/bin/env python3
"""
Solidity file preprocessor for making standalone .sol files compilable by Slither.

Handles three scenarios:
1. Code fragments (no pragma/contract keyword): wraps in a minimal contract
2. Files with missing imports: strips imports, generates inline stubs
3. Iterative compilation: parses solc errors and generates stubs until success
"""

import os
import re
import json
import shutil
import hashlib
import logging
import tempfile
import subprocess
from pathlib import Path

logger = logging.getLogger("SolPreprocessor")


# ---------------------------------------------------------------------------
# Common OpenZeppelin stub definitions
# ---------------------------------------------------------------------------
OZ_STUBS = """
// === Auto-generated stubs for missing imports ===
abstract contract Ownable {
    address internal _owner;
    modifier onlyOwner() { _; }
    function owner() public view virtual returns (address) { return _owner; }
    function renounceOwnership() public virtual {}
    function transferOwnership(address newOwner) public virtual {}
}
abstract contract OwnableUpgradeable {
    address internal _owner;
    modifier onlyOwner() { _; }
    function owner() public view virtual returns (address) { return _owner; }
    function __Ownable_init() internal virtual {}
}
abstract contract Initializable {
    modifier initializer() { _; }
    modifier reinitializer(uint8 version) { _; }
}
abstract contract ReentrancyGuard {
    modifier nonReentrant() { _; }
}
abstract contract ReentrancyGuardUpgradeable {
    modifier nonReentrant() { _; }
    function __ReentrancyGuard_init() internal virtual {}
}
abstract contract PausableUpgradeable {
    modifier whenNotPaused() { _; }
    modifier whenPaused() { _; }
    function _pause() internal virtual {}
    function _unpause() internal virtual {}
    function paused() public view virtual returns (bool) { return false; }
    function __Pausable_init() internal virtual {}
}
abstract contract Pausable {
    modifier whenNotPaused() { _; }
    modifier whenPaused() { _; }
    function _pause() internal virtual {}
    function _unpause() internal virtual {}
    function paused() public view virtual returns (bool) { return false; }
}
abstract contract AccessControl {
    modifier onlyRole(bytes32 role) { _; }
    function hasRole(bytes32 role, address account) public view virtual returns (bool) { return false; }
    function _grantRole(bytes32 role, address account) internal virtual {}
    function _revokeRole(bytes32 role, address account) internal virtual {}
    function getRoleAdmin(bytes32 role) public view virtual returns (bytes32) { return bytes32(0); }
    function grantRole(bytes32 role, address account) public virtual {}
    function revokeRole(bytes32 role, address account) public virtual {}
}
abstract contract AccessControlUpgradeable {
    modifier onlyRole(bytes32 role) { _; }
    function hasRole(bytes32 role, address account) public view virtual returns (bool) { return false; }
    function _grantRole(bytes32 role, address account) internal virtual {}
    function __AccessControl_init() internal virtual {}
}
abstract contract AccessControlEnumerable is AccessControl {}

interface IERC20 {
    function totalSupply() external view returns (uint256);
    function balanceOf(address account) external view returns (uint256);
    function transfer(address to, uint256 amount) external returns (bool);
    function allowance(address owner, address spender) external view returns (uint256);
    function approve(address spender, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}
interface IERC20Upgradeable {
    function totalSupply() external view returns (uint256);
    function balanceOf(address account) external view returns (uint256);
    function transfer(address to, uint256 amount) external returns (bool);
    function allowance(address owner, address spender) external view returns (uint256);
    function approve(address spender, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}
interface IERC20Metadata is IERC20 {
    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function decimals() external view returns (uint8);
}
interface IERC20MetadataUpgradeable is IERC20Upgradeable {
    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function decimals() external view returns (uint8);
}
abstract contract ERC20 is IERC20 {
    mapping(address => uint256) internal _balances;
    mapping(address => mapping(address => uint256)) internal _allowances;
    uint256 internal _totalSupply;
    string internal _name;
    string internal _symbol;
    function name() public view virtual returns (string memory) { return _name; }
    function symbol() public view virtual returns (string memory) { return _symbol; }
    function decimals() public view virtual returns (uint8) { return 18; }
    function totalSupply() public view virtual override returns (uint256) { return _totalSupply; }
    function balanceOf(address account) public view virtual override returns (uint256) { return _balances[account]; }
    function _mint(address account, uint256 amount) internal virtual {}
    function _burn(address account, uint256 amount) internal virtual {}
    function _transfer(address from, address to, uint256 amount) internal virtual {}
    function _approve(address owner, address spender, uint256 amount) internal virtual {}
}
abstract contract ERC20Upgradeable is IERC20Upgradeable {
    mapping(address => uint256) internal _balances;
    mapping(address => mapping(address => uint256)) internal _allowances;
    uint256 internal _totalSupply;
    function _mint(address account, uint256 amount) internal virtual {}
    function _burn(address account, uint256 amount) internal virtual {}
    function _transfer(address from, address to, uint256 amount) internal virtual {}
    function __ERC20_init(string memory name_, string memory symbol_) internal virtual {}
}
abstract contract ERC20SnapshotUpgradeable is ERC20Upgradeable {}
interface IERC721 {
    function balanceOf(address owner) external view returns (uint256);
    function ownerOf(uint256 tokenId) external view returns (address);
    function transferFrom(address from, address to, uint256 tokenId) external;
    function safeTransferFrom(address from, address to, uint256 tokenId) external;
}
interface IERC721Upgradeable {
    function balanceOf(address owner) external view returns (uint256);
    function ownerOf(uint256 tokenId) external view returns (address);
}
interface IERC721ReceiverUpgradeable {
    function onERC721Received(address, address, uint256, bytes calldata) external returns (bytes4);
}
abstract contract ERC721 {
    function _mint(address to, uint256 tokenId) internal virtual {}
    function _burn(uint256 tokenId) internal virtual {}
    function ownerOf(uint256 tokenId) public view virtual returns (address) {}
}
abstract contract ERC721Upgradeable {
    function _mint(address to, uint256 tokenId) internal virtual {}
    function _burn(uint256 tokenId) internal virtual {}
    function __ERC721_init(string memory name_, string memory symbol_) internal virtual {}
}
interface IERC1155Upgradeable {}
interface IERC1155ReceiverUpgradeable {}

library SafeERC20 {
    function safeTransfer(IERC20 token, address to, uint256 value) internal {}
    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {}
    function safeApprove(IERC20 token, address spender, uint256 value) internal {}
}
library SafeERC20Upgradeable {
    function safeTransfer(IERC20Upgradeable token, address to, uint256 value) internal {}
    function safeTransferFrom(IERC20Upgradeable token, address from, address to, uint256 value) internal {}
    function safeApprove(IERC20Upgradeable token, address spender, uint256 value) internal {}
}
library SafeMath {
    function add(uint256 a, uint256 b) internal pure returns (uint256) { return a + b; }
    function sub(uint256 a, uint256 b) internal pure returns (uint256) { return a - b; }
    function mul(uint256 a, uint256 b) internal pure returns (uint256) { return a * b; }
    function div(uint256 a, uint256 b) internal pure returns (uint256) { return a / b; }
    function mod(uint256 a, uint256 b) internal pure returns (uint256) { return a % b; }
}
library SafeMathUpgradeable {
    function add(uint256 a, uint256 b) internal pure returns (uint256) { return a + b; }
    function sub(uint256 a, uint256 b) internal pure returns (uint256) { return a - b; }
    function mul(uint256 a, uint256 b) internal pure returns (uint256) { return a * b; }
    function div(uint256 a, uint256 b) internal pure returns (uint256) { return a / b; }
}
library SafeCast {
    function toUint256(int256 value) internal pure returns (uint256) { return uint256(value); }
    function toInt256(uint256 value) internal pure returns (int256) { return int256(value); }
    function toUint128(uint256 value) internal pure returns (uint128) { return uint128(value); }
}
library Math {
    function max(uint256 a, uint256 b) internal pure returns (uint256) { return a >= b ? a : b; }
    function min(uint256 a, uint256 b) internal pure returns (uint256) { return a < b ? a : b; }
}
library Address {
    function isContract(address account) internal view returns (bool) { return account.code.length > 0; }
    function sendValue(address payable recipient, uint256 amount) internal {}
}
library AddressUpgradeable {
    function isContract(address account) internal view returns (bool) { return account.code.length > 0; }
}
library EnumerableSet {
    struct Bytes32Set { bytes32[] _values; }
    struct AddressSet { bytes32[] _values; }
    struct UintSet { bytes32[] _values; }
}
library EnumerableSetUpgradeable {
    struct Bytes32Set { bytes32[] _values; }
    struct AddressSet { bytes32[] _values; }
    struct UintSet { bytes32[] _values; }
}
library StringsUpgradeable {
    function toString(uint256 value) internal pure returns (string memory) { return ""; }
}
library MerkleProofUpgradeable {
    function verify(bytes32[] memory proof, bytes32 root, bytes32 leaf) internal pure returns (bool) { return true; }
}
library ClonesUpgradeable {
    function clone(address implementation) internal returns (address) { return address(0); }
}
library Clones {
    function clone(address implementation) internal returns (address) { return address(0); }
}
library ECDSA {
    function recover(bytes32 hash, bytes memory signature) internal pure returns (address) { return address(0); }
}
library FixedPointMathLib {
    function mulDivDown(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) { return (x * y) / d; }
    function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) { return (x * y + d - 1) / d; }
}
library FullMath {
    function mulDiv(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256) { return (a * b) / denominator; }
}
abstract contract ERC4626 is ERC20 {}
// === End auto-generated stubs ===
"""

# Stubs that are safe at pragma >=0.4.0 (no abstract, simpler syntax)
OZ_STUBS_LEGACY = """
// === Auto-generated stubs (legacy) ===
contract Ownable {
    address internal _owner;
    modifier onlyOwner() { _; }
    function owner() public view returns (address) { return _owner; }
}
interface IERC20 {
    function totalSupply() external view returns (uint256);
    function balanceOf(address account) external view returns (uint256);
    function transfer(address to, uint256 amount) external returns (bool);
    function allowance(address owner, address spender) external view returns (uint256);
    function approve(address spender, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}
library SafeMath {
    function add(uint256 a, uint256 b) internal pure returns (uint256) { return a + b; }
    function sub(uint256 a, uint256 b) internal pure returns (uint256) { return a - b; }
    function mul(uint256 a, uint256 b) internal pure returns (uint256) { return a * b; }
    function div(uint256 a, uint256 b) internal pure returns (uint256) { return a / b; }
}
library SafeERC20 {
    function safeTransfer(IERC20 token, address to, uint256 value) internal {}
    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {}
}
library Address {
    function isContract(address account) internal view returns (bool) { return account.code.length > 0; }
}
library EnumerableSet {
    struct Bytes32Set { bytes32[] _values; }
    struct AddressSet { bytes32[] _values; }
    struct UintSet { bytes32[] _values; }
}
// === End stubs (legacy) ===
"""


def _detect_pragma_version(content):
    """Extract the pragma version from content. Returns (major, minor) or None."""
    m = re.search(r'pragma\s+solidity\s*[>=^~]*\s*(\d+)\.(\d+)', content)
    if m:
        return (int(m.group(1)), int(m.group(2)))
    return None


def _is_modern_solidity(content):
    """Check if file uses Solidity >= 0.6.0 features (abstract, override, etc.)."""
    ver = _detect_pragma_version(content)
    if ver and ver >= (0, 6):
        return True
    # Heuristic: check for 'abstract contract' or 'override' keywords
    if re.search(r'\babstract\s+contract\b', content):
        return True
    return ver is None  # Default to modern if unknown


def _extract_imports(content):
    """Extract all import statements and their details."""
    imports = []
    for m in re.finditer(r'^\s*(import\s+.+?;)', content, re.MULTILINE | re.DOTALL):
        imp_line = m.group(1).replace('\n', ' ')
        # Extract path
        path_m = re.search(r'["\']([^"\']+)["\']', imp_line)
        path = path_m.group(1) if path_m else ""
        # Extract named imports
        names = []
        names_m = re.search(r'\{([^}]+)\}', imp_line)
        if names_m:
            names = [n.strip().split(' as ')[0].strip() for n in names_m.group(1).split(',')]
        imports.append({
            "line": imp_line,
            "path": path,
            "names": names,
            "start": m.start(),
            "end": m.end(),
        })
    return imports


def _extract_base_contracts(content):
    """Extract base contract names from inheritance declarations."""
    bases = set()
    for m in re.finditer(r'\b(?:contract|interface|library|abstract\s+contract)\s+\w+\s+is\s+([^{]+)', content):
        base_str = m.group(1)
        # Parse comma-separated, handle generics like ERC20("name", "sym")
        depth = 0
        current = ""
        for ch in base_str:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            elif ch == ',' and depth == 0:
                name = current.strip().split('(')[0].strip()
                if name:
                    bases.add(name)
                current = ""
                continue
            current += ch
        name = current.strip().split('(')[0].strip()
        if name:
            bases.add(name)
    return bases


def _extract_used_types(content):
    """Extract type names used in the contract body that might need stubs."""
    types = set()
    # Interface/library usage: IERC20(addr), SafeERC20.safeTransfer, etc.
    for m in re.finditer(r'\b([A-Z][A-Za-z0-9_]+)\s*[.(]', content):
        types.add(m.group(1))
    # Type declarations in function params/returns
    for m in re.finditer(r'\b([A-Z][A-Za-z0-9_]+)\s+(?:memory|storage|calldata|internal|external|public|private)', content):
        types.add(m.group(1))
    return types


# Names that are already defined in OZ_STUBS
STUBBED_NAMES = {
    'Ownable', 'OwnableUpgradeable', 'Initializable',
    'ReentrancyGuard', 'ReentrancyGuardUpgradeable',
    'PausableUpgradeable', 'Pausable',
    'AccessControl', 'AccessControlUpgradeable', 'AccessControlEnumerable',
    'IERC20', 'IERC20Upgradeable', 'IERC20Metadata', 'IERC20MetadataUpgradeable',
    'ERC20', 'ERC20Upgradeable', 'ERC20SnapshotUpgradeable',
    'IERC721', 'IERC721Upgradeable', 'IERC721ReceiverUpgradeable',
    'ERC721', 'ERC721Upgradeable',
    'IERC1155Upgradeable', 'IERC1155ReceiverUpgradeable',
    'SafeERC20', 'SafeERC20Upgradeable',
    'SafeMath', 'SafeMathUpgradeable', 'SafeCast',
    'Math', 'Address', 'AddressUpgradeable',
    'EnumerableSet', 'EnumerableSetUpgradeable',
    'StringsUpgradeable', 'MerkleProofUpgradeable',
    'ClonesUpgradeable', 'Clones', 'ECDSA',
    'FixedPointMathLib', 'FullMath', 'ERC4626',
}

# Solidity built-in types that don't need stubs
BUILTIN_TYPES = {
    'uint256', 'uint128', 'uint64', 'uint32', 'uint16', 'uint8',
    'int256', 'int128', 'int64', 'int32', 'int16', 'int8',
    'address', 'bool', 'string', 'bytes', 'bytes32', 'bytes4',
    'mapping', 'Array', 'Event', 'Error', 'Type',
}


def _generate_dynamic_stubs(base_contracts, used_types, imported_names, content):
    """Generate stub declarations for types not covered by OZ_STUBS."""
    stubs = []
    all_names_needing_stubs = set()

    # Bases from inheritance
    for base in base_contracts:
        if base not in STUBBED_NAMES and base not in BUILTIN_TYPES:
            all_names_needing_stubs.add(base)

    # Named imports
    for name in imported_names:
        if name not in STUBBED_NAMES and name not in BUILTIN_TYPES:
            all_names_needing_stubs.add(name)

    # Filter: only add stubs for names not already defined in the file
    defined_names = set()
    for m in re.finditer(r'\b(?:contract|interface|library|abstract\s+contract|struct|enum)\s+(\w+)', content):
        defined_names.add(m.group(1))

    for name in sorted(all_names_needing_stubs):
        if name in defined_names:
            continue
        # Determine type based on naming convention
        if name.startswith('I') and name[1:2].isupper():
            stubs.append(f"interface {name} {{}}")
        elif 'Lib' in name or 'Math' in name or 'Helper' in name or 'Utils' in name:
            stubs.append(f"library {name} {{}}")
        else:
            stubs.append(f"interface {name} {{}}")  # Default to interface (safest)

    return "\n".join(stubs)


def preprocess_sol_file(sol_path, output_dir=None):
    """
    Preprocess a Solidity file to make it compilable by Slither.

    Returns:
        Path to the preprocessed file (may be the original if no changes needed).
    """
    sol_path = Path(sol_path)
    content = sol_path.read_text(errors='ignore')

    has_pragma = bool(re.search(r'pragma\s+solidity', content))
    has_contract = bool(re.search(r'\b(?:contract|interface|library)\b', content))
    has_imports = bool(re.search(r'^\s*import\s+', content, re.MULTILINE))

    # No preprocessing needed: has pragma, has contract, no imports
    if has_pragma and has_contract and not has_imports:
        return sol_path

    # Create output directory
    if output_dir is None:
        output_dir = Path(tempfile.mkdtemp(prefix='acfix_prep_'))
    else:
        output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # --- Case 1: Code fragment (no pragma / no contract) ---
    if not has_contract:
        return _wrap_fragment(content, sol_path.name, output_dir)

    # --- Case 2: Has imports to resolve ---
    if has_imports:
        return _strip_and_stub(content, sol_path.name, output_dir)

    # --- Case 3: Has contract but no pragma ---
    if not has_pragma:
        new_content = "pragma solidity >=0.4.0 <0.9.0;\n" + content
        out_path = output_dir / sol_path.name
        out_path.write_text(new_content)
        return out_path

    return sol_path


def _wrap_fragment(content, filename, output_dir):
    """Wrap a code fragment in a minimal compilable contract."""
    lines = content.strip().splitlines()

    # Detect if it uses Solidity 0.8+ features
    uses_modern = any(kw in content for kw in ['unchecked', 'revert ', 'custom error'])

    # Determine pragma
    pragma_version = "pragma solidity >=0.8.0;" if uses_modern else "pragma solidity >=0.4.0 <0.9.0;"

    # Collect referenced but undefined symbols
    # Common patterns in fragments: _allowances, _owner, _mint, _burn, _transfer, etc.
    needs_erc20_base = any(s in content for s in ['_allowances', '_mint(', '_burn(', '_transfer(', '_approve(', 'totalSupply'])
    needs_ownable = '_owner' in content or 'onlyOwner' in content
    needs_events = bool(re.search(r'\bemit\s+(\w+)', content))

    # Build contract body
    contract_name = Path(filename).stem.replace('-', '_').replace('.', '_')
    if not contract_name[0].isalpha():
        contract_name = 'C_' + contract_name

    inheritance = []
    preamble_lines = [pragma_version, ""]

    if needs_erc20_base:
        preamble_lines.append("interface IERC20 { function totalSupply() external view returns (uint256); function balanceOf(address) external view returns (uint256); function transfer(address, uint256) external returns (bool); function allowance(address, address) external view returns (uint256); function approve(address, uint256) external returns (bool); function transferFrom(address, address, uint256) external returns (bool); }")
        preamble_lines.append("abstract contract ERC20Base { mapping(address => uint256) internal _balances; mapping(address => mapping(address => uint256)) internal _allowances; uint256 internal _totalSupply; function _mint(address, uint256) internal virtual {} function _burn(address, uint256) internal virtual {} function _transfer(address, address, uint256) internal virtual {} function _approve(address, address, uint256) internal virtual {} function _msgSender() internal view virtual returns (address) { return msg.sender; } function msgSender() internal view virtual returns (address) { return msg.sender; } }")
        inheritance.append("ERC20Base")

    if needs_ownable and not needs_erc20_base:
        preamble_lines.append("abstract contract OwnableBase { address internal _owner; modifier onlyOwner() { _; } }")
        inheritance.append("OwnableBase")

    # Extract event names referenced in the fragment
    if needs_events:
        events = set(re.findall(r'\bemit\s+(\w+)\s*\(', content))
        for ev in events:
            preamble_lines.append(f"// event {ev}(...) - auto stub")

    # Check for modifiers used
    modifiers_used = set(re.findall(r'\)\s+(external|public|internal|private)\s+(\w+)\s*\{', content))
    for _, mod_name in modifiers_used:
        if mod_name not in ('returns', 'override', 'virtual', 'view', 'pure', 'payable'):
            preamble_lines.append(f"// modifier {mod_name} referenced")

    inh_str = f" is {', '.join(inheritance)}" if inheritance else ""
    preamble_lines.append(f"contract {contract_name}{inh_str} {{")

    # Handle 'emit' events - declare them inside the contract
    if needs_events:
        events = set(re.findall(r'\bemit\s+(\w+)\s*\(', content))
        for ev in events:
            preamble_lines.append(f"    event {ev}(address indexed, uint256);")

    # Check for 'nonReentrant' or other modifiers
    if 'nonReentrant' in content:
        preamble_lines.append("    modifier nonReentrant() { _; }")

    # Add the fragment content (re-indent if needed)
    for line in lines:
        preamble_lines.append("    " + line if line.strip() and not line.startswith('    ') else line)

    preamble_lines.append("}")

    out_path = output_dir / filename
    out_path.write_text("\n".join(preamble_lines))
    return out_path


def _strip_and_stub(content, filename, output_dir):
    """Strip import statements and add stub definitions."""
    imports = _extract_imports(content)
    base_contracts = _extract_base_contracts(content)
    is_modern = _is_modern_solidity(content)

    # Collect all imported names
    imported_names = set()
    for imp in imports:
        imported_names.update(imp['names'])
        # For path-only imports, extract likely contract name from path
        if not imp['names']:
            path_stem = Path(imp['path']).stem
            imported_names.add(path_stem)

    # Comment out all import lines
    new_content = content
    for imp in reversed(imports):  # Reverse to preserve positions
        new_content = new_content[:imp['start']] + "// " + new_content[imp['start']:]

    # Add pragma if missing
    if not re.search(r'pragma\s+solidity', new_content):
        new_content = "pragma solidity >=0.8.0;\n" + new_content

    # Determine which stub set to use
    stubs = OZ_STUBS if is_modern else OZ_STUBS_LEGACY

    # Generate dynamic stubs for names not in OZ_STUBS
    dynamic_stubs = _generate_dynamic_stubs(
        base_contracts, set(), imported_names, new_content
    )

    # Find insertion point: after pragma, before first contract/interface/library
    pragma_end = 0
    m = re.search(r'pragma\s+solidity[^;]+;', new_content)
    if m:
        pragma_end = m.end()

    # Insert stubs after pragma
    new_content = (
        new_content[:pragma_end] +
        "\n" + stubs + "\n" +
        dynamic_stubs + "\n" +
        new_content[pragma_end:]
    )

    # Fix inheritance: strip base contracts that reference hardhat/console
    new_content = new_content.replace('import "hardhat/console.sol";', '// import "hardhat/console.sol";')
    # Replace console.log calls with nothing
    new_content = re.sub(r'\bconsole\.log\s*\([^)]*\)\s*;', '// console.log removed', new_content)

    out_path = output_dir / filename
    out_path.write_text(new_content)
    return out_path


def preprocess_batch(sol_files, output_base_dir):
    """
    Preprocess a batch of Solidity files.

    Args:
        sol_files: list of Path objects
        output_base_dir: base directory for preprocessed files

    Returns:
        dict mapping original path -> preprocessed path
    """
    output_base = Path(output_base_dir)
    output_base.mkdir(parents=True, exist_ok=True)
    result = {}
    for sol in sol_files:
        sol = Path(sol)
        # Create per-file output dir to avoid name collisions
        file_hash = hashlib.md5(str(sol).encode()).hexdigest()[:8]
        file_dir = output_base / f"{sol.stem}_{file_hash}"
        try:
            preprocessed = preprocess_sol_file(sol, file_dir)
            result[str(sol)] = str(preprocessed)
            logger.debug(f"Preprocessed {sol.name} -> {preprocessed}")
        except Exception as e:
            logger.warning(f"Failed to preprocess {sol.name}: {e}")
            result[str(sol)] = str(sol)  # Fallback to original
    return result
