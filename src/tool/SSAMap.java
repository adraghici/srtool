package tool;

import java.util.HashMap;
import java.util.Map;

public class SSAMap {
    private static final Integer DEFAULT_ID = 0;
    private final Map<String, Integer> nextID;

    public SSAMap() {
        nextID = new HashMap<>();
    }

    public int id(String var) {
        if (nextID.containsKey(var)) {
            return nextID.get(var);
        }
        return DEFAULT_ID;
    }

    public int fresh(String var) {
        return id(var) + 1;
    }

    public void update(String var, int id) {
        nextID.put(var, id);
    }
}
