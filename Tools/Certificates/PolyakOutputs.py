"""Exact local outputs regenerated from the external Heavy-Ball archive.

Keep this dependency-free manifest shared by preparation and cleanup. Handwritten
proofs, source descriptors and documentation are deliberately absent.
"""

P2_FILES = {
    "polyak/Boundary/P2/Chebyshev.lean", "polyak/Boundary/P2/SlackSource.lean",
    *{"polyak/Certificates/" + name + ".lean" for name in
      ("P2Codes", "P2Signs", "P2Identities", "P2Endpoints", "P2Slacks")},
    *{f"polyak/Certificates/P2SlacksData{index:02d}.lean" for index in range(10)},
}
P5_FILES = {"polyak/Certificates/P5System.lean", "polyak/Certificates/P5Critical.lean",
            *{"polyak/Boundary/P5/" + name + ".lean" for name in
              ("CriticalSystem", "CriticalJacobian", "CriticalMatrix")}}
STARTUP_FILES = {*{f"polyak/Certificates/Startup/Check{index:02d}.lean" for index in range(44)},
                 *{f"polyak/Certificates/Startup/Code{index:02d}.lean" for index in range(17)},
                 "polyak/Certificates/Startup/Codes.lean", "polyak/Certificates/Startup/Signs.lean"}
CONTINUATION_FILES = {f"polyak/Certificates/Continuation/{family}Source.lean"
                      for family in ("P1", "P5")}
CONTINUATION_FILES |= {f"polyak/Certificates/Continuation/P1Batches/Batch{index:03d}.lean"
                       for index in range(16)} | {"polyak/Certificates/Continuation/P1Cover.lean"}
CONTINUATION_FILES |= {f"polyak/Certificates/Continuation/P1Geometry/Batch{index:03d}.lean"
                       for index in range(16)} | {"polyak/Certificates/Continuation/P1Geometry.lean"}
CONTINUATION_FILES |= {f"polyak/Certificates/Continuation/P5Batches/Batch{index:03d}.lean"
                       for index in range(20)} | {"polyak/Certificates/Continuation/P5Cover.lean"}
CONTINUATION_FILES |= {f"polyak/Certificates/Continuation/P5Links/Link{index:03d}.lean"
                       for index in range(19)} | {"polyak/Certificates/Continuation/P5Family.lean"}
EXPECTED = P2_FILES | P5_FILES | STARTUP_FILES | CONTINUATION_FILES
P1_SLACK_FILES = {f"polyak/Certificates/P1Slacks/Lag{index:02d}Lower.lean"
                  for index in range(2,13)} | {
                    f"polyak/Certificates/P1Slacks/Lag{index:02d}Upper.lean"
                    for index in (1,*range(4,13))}
EXPECTED |= P1_SLACK_FILES


P1_SLOPE_FILES = {f"polyak/Certificates/Continuation/P1Slope/Batch{index:03d}.lean"
                  for index in range(16)} | {"polyak/Certificates/Continuation/P1Slope.lean"}
EXPECTED |= P1_SLOPE_FILES
P5_LAG_FILES = {"polyak/Certificates/Continuation/P5LagCodes.lean"}
EXPECTED |= P5_LAG_FILES
P5_PROPERTY_FILES = {f"polyak/Certificates/Continuation/P5Prefix/Batch{index:03d}.lean"
                     for index in range(20)} | {"polyak/Certificates/Continuation/P5Properties.lean"}
EXPECTED |= P5_PROPERTY_FILES
EXPECTED |= {"polyak/Certificates/Continuation/P5EndpointGraphs.lean"}
P5_SLOPE_FILES = {f"polyak/Certificates/Continuation/P5Slope/Batch{index:03d}.lean"
                  for index in range(20)} | {"polyak/Certificates/Continuation/P5Slope.lean"}
EXPECTED |= P5_SLOPE_FILES
