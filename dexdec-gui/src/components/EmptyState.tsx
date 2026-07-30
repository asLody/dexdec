import type { ReactNode } from "react";

export function EmptyState({
  icon,
  title,
  action,
  compact = false,
}: {
  icon?: ReactNode;
  title: string;
  action?: ReactNode;
  compact?: boolean;
}) {
  return (
    <div className={`empty-state ${compact ? "is-compact" : ""}`}>
      {icon ? <div className="empty-state-icon" aria-hidden="true">{icon}</div> : null}
      <div className="empty-state-title">{title}</div>
      {action ? <div className="empty-state-action">{action}</div> : null}
    </div>
  );
}
