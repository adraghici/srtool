package ast;

import java.util.List;

/**
 * Interface used to model a simple node used in the Abstract Syntax Tree built after parsing.
 */
public interface Node {

    /**
     * Returns the nodes that should be visited from the current node.
     */
    List<Node> getChildren();
}
