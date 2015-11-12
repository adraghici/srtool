package ast;

import java.util.List;
import java.util.Set;

/**
 * Interface used to model a simple node used in the Abstract Syntax Tree built after parsing.
 */
public interface Node {

    /**
     * Returns all the variables modified in the current node.
     */
    Set<String> getModset();

    /**
     * Returns the nodes that should be visited from the current node.
     */
    List<Node> getChildren();
}
