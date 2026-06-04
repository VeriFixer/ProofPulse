export interface RunSession {
  id: number;
  abortController: AbortController;
  file: string;
}

let currentSession: RunSession | null = null;
let sessionCounter = 0;

/**
 * Creates a new RunSession, aborting any prior session's AbortController.
 * Increments the session counter to guarantee unique IDs.
 */
export function startNewSession(file: string): RunSession {
  if (currentSession) {
    currentSession.abortController.abort();
  }
  sessionCounter++;
  currentSession = {
    id: sessionCounter,
    abortController: new AbortController(),
    file,
  };
  return currentSession;
}

/** Returns true only if the given session's ID matches the latest session's ID. */
export function isSessionCurrent(session: RunSession): boolean {
  return currentSession !== null && session.id === currentSession.id;
}

/** Returns the current session, or null if none exists. */
export function getCurrentSession(): RunSession | null {
  return currentSession;
}
