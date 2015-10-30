package tool;

import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

public class Scopes {
    private final IdMap idMap;
    private final Deque<Map<String, Integer>> scopes;

    /**
     * This will enter a default scope when created.
     */
    public Scopes() {
        idMap = new IdMap();
        scopes = new LinkedList<>();
        scopes.add(new HashMap<>());
    }

    public void enterScope() {
        scopes.add(new HashMap<>(scopes.getLast()));
    }

    public void exitScope() {
        scopes.pop();
    }

    public void declareVar(String var) {
        scopes.getLast().put(var, idMap.fresh(var));
    }

    public String getVar(String var) {
        return var + scopes.getLast().get(var);
    }
}
