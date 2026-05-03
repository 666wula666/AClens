import json
import logging
from typing import List, Dict, Any

logger = logging.getLogger(__name__)

class BaselineParser:
    """
    Standardizes outputs from various tools (Slither, Mythril, etc.) 
    into a common ACLens report format for comparison.
    Target Format:
    {
      "file": "contract.sol",
      "vuln_type": "Reentrancy",
      "line": 42,
      "tool": "Slither"
    }
    """

    @staticmethod
    def parse_slither(json_path: str) -> List[Dict[str, Any]]:
        results = []
        try:
            with open(json_path, 'r') as f:
                data = json.load(f)
            
            # Handle standard Slither JSON output
            # 'results' -> 'detectors'
            detectors = data.get('results', {}).get('detectors', [])
            if not detectors and isinstance(data, list):
                 detectors = data # Sometimes it's a list directly

            for d in detectors:
                check = d.get('check', 'Unknown')
                # Extract line number from elements
                line = 0
                file_name = ""
                if d.get('elements'):
                    first_elem = d['elements'][0]
                    if 'source_mapping' in first_elem:
                        line = first_elem['source_mapping'].get('lines', [0])[0]
                        file_name = first_elem['source_mapping'].get('filename_relative', '')
                
                results.append({
                    "file": file_name,
                    "vuln_type": check,
                    "line": line,
                    "tool": "Slither"
                })
        except Exception as e:
            logger.error(f"Error parsing Slither JSON {json_path}: {e}")
        return results

    @staticmethod
    def parse_mythril(json_path: str) -> List[Dict[str, Any]]:
        results = []
        try:
            with open(json_path, 'r') as f:
                data = json.load(f)
            
            issues = data.get('issues', [])
            for issue in issues:
                results.append({
                    "file": issue.get('filename', ''),
                    "vuln_type": issue.get('title', 'Unknown'),
                    "line": issue.get('lineno', 0),
                    "tool": "Mythril"
                })
        except Exception as e:
            logger.error(f"Error parsing Mythril JSON {json_path}: {e}")
        return results
