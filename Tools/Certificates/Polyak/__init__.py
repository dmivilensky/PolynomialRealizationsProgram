"""Local Lean proposal templates consuming an already configured math archive.

Payload.configure selects and validates the external data before this entrypoint
is called.  No producer module or executable archive payload is imported.
"""


def generate_all(root=None):
    """Generate the complete local certificate manifest and return its paths."""
    from . import continuation_boxes, continuation_geometry, continuation_lean, continuation_slope
    from . import continuation_p5_geometry, continuation_p5_slope
    from . import p1_slacks_lean, p2_lean, p5_lags_lean, p5_lean, startup_codes
    from . import p5_endpoint_lean
    from ..PolyakOutputs import EXPECTED

    paths = [*p2_lean.generate_all(root),
             *p5_lean.generate_all(root),
             *startup_codes.generate_all(root),
             *continuation_lean.generate_all(root),
             *continuation_boxes.generate_all(root),
             *continuation_boxes.generate_central(root),
             *continuation_boxes.generate_central_links(root),
             *continuation_geometry.generate(root),
             *continuation_slope.generate(root),
             *p1_slacks_lean.generate(root),
             *p5_lags_lean.generate(root),
             *continuation_p5_geometry.generate(root),
             *continuation_p5_slope.generate(root),
             *p5_endpoint_lean.generate(root)]
    if len(paths) != len(EXPECTED) or set(paths) != EXPECTED:
        raise ValueError("the Polyak templates differ from the shared output manifest")
    return paths
