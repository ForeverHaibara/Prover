from sympy.core import Basic
from sympy.core.traversal import postorder_traversal

from .tractable import Tractable

def write_full_proof(obj: Basic):
    """
    Write a full proof of the given object.
    """
    written = set()
    proof = []
    for node in postorder_traversal(obj):
        if isinstance(node, Tractable):
            _id = node # id(node)
            if _id in written:
                continue
            written.add(_id)
            s = node.describe().strip()
            if len(s):
                proof.append(s)

    proof = '\n\n'.join(proof)
    return proof