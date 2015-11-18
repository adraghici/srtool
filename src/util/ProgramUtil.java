package util;

import ast.Node;
import ast.Program;
import visitor.PruningVisitor;
import visitor.Visitor;

import java.util.Collections;
import java.util.List;

public class ProgramUtil {
    /**
     * Transforms a program by traversing it with the given visitors sequentially and adds the string
     * representation of the new state to the given list.
     */
    public static Program transform(Program program, List<Visitor> visitors, List<String> states) {
        Program dirty = program;
        for (Visitor visitor : visitors) {
            dirty = transform(dirty, visitor, states);
        }
        return dirty;
    }

    /**
     * Returns a new program obtained by pruning specific nodes in the given one.
     */
    public static Program prune(Program program, List<Node> nodes, List<String> states) {
        return transform(program, new PruningVisitor(nodes), states);
    }

    /**
     * Returns a clean stage copy of the given program
     */
    public static Program clean(Program program, List<String> states) {
        return transform(program, new PruningVisitor(Collections.emptyList()), states);
    }

    /**
     * Transforms a program by traversing it with the given visitor and adds the string representation
     * of the new state to the given list.
     */
    private static Program transform(Program program, Visitor visitor, List<String> states) {
        Program result = (Program) visitor.visit(program);
        states.add(result.toString(visitor));
        return result;
    }
}
