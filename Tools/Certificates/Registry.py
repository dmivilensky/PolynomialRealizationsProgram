"""Workspace-owned converters for data-only certificate sources.

Source.json is solely a transport/byte-identity contract. Converter selection
belongs to the consumer, never to an archive or its supplier. Keys are Lake
package directories, relative to the workspace; discovery of Lean packages
remains independent of this optional registration.
"""

PREPARATIONS = {
    "chebyshev2": {
        "Certificates/Source.json": {
            "module": "Tools.Certificates.ChebyshevPrepare",
        },
    },
    "polyak": {
        "Certificates/Source.json": {
            "module": "Tools.Certificates.PolyakPrepare",
            "requirements": "Tools/Certificates/Polyak/requirements.txt",
        },
        "Certificates/PartII/Source.json": {
            "module": "Tools.Certificates.PolyakPartIIPrepare",
        },
    },
}
