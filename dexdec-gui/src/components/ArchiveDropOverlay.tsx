import { useTranslation } from "../i18n";

interface ArchiveDropOverlayProps {
  accepted: boolean;
  displayName: string;
}

export function ArchiveDropOverlay({
  accepted,
  displayName,
}: ArchiveDropOverlayProps) {
  const { t } = useTranslation();
  // What is being dropped answers itself; only a refusal has to be explained.
  const note = accepted ? displayName : t("drop.unsupported");

  return (
    <div className="archive-drop-overlay" data-accepted={accepted}>
      {note ? <span className="archive-drop-note">{note}</span> : null}
    </div>
  );
}
