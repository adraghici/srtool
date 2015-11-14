package ast;

import visitor.Visitor;

import java.util.Collections;
import java.util.List;
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
     * Returns the nodes that should be visited from the current node.
     */
    default List<Node> getChildren() {
        return Collections.emptyList();
    }

    /**
     * Sets the children of the current node from the given list.
     */
    default void setChildren(List<Node> children) {}

    /**
     * Used for visitor pattern.
     */
    Object accept(Visitor visitor);
}
