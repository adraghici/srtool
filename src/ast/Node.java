package ast;

import visitor.Visitor;

import java.util.Collections;
import java.util.Set;

/**
 * Interface used to model a simple node used in the Abstract Syntax Tree built after parsing.
 */
public interface Node {

    /**
     * Returns all the variables modified in the current node.
     */
    default Set<String> getModified() {
        return Collections.emptySet();
    }

    /**
     * Used for visitor pattern.
     */
    Object accept(Visitor visitor);
}
