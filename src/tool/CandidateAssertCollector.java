package tool;

import ast.AssertStmt;
import ast.Node;
import ast.TraceableNode;
import ast.TraceableNode.SourceType;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import java.util.List;
import java.util.stream.Collectors;

public class CandidateAssertCollector {
    private final BiMap<AssertStmt, TraceableNode> assertOrigin;

    public CandidateAssertCollector() {
        assertOrigin = HashBiMap.create();
    }

    public void add(TraceableNode parent, AssertStmt assertStmt) {
        while (parent.getSource().isPresent() && parent.getSourceType() != SourceType.REMOVING) {
            parent = parent.getSource().get();
        }
        assertOrigin.put(assertStmt.getOriginal() != null ? assertStmt.getOriginal() : assertStmt, parent);
    }

    public List<Node> resolve(List<AssertStmt> assertStmts) {
        return assertStmts.stream()
            .filter(assertOrigin::containsKey)
            .map(assertOrigin::get)
            .collect(Collectors.toList());
    }

    public void clear() {
        assertOrigin.clear();
    }
}
