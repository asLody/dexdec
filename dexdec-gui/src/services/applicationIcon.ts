import type { Archive } from "../domain/models";
import { AndroidProjectIndex } from "../domain/xmlNavigation";
import { decompilerClient } from "./decompilerClient";

export class ApplicationIconService {
  constructor(private readonly archive: Archive) {}

  async load(): Promise<string | null> {
    const path = this.resourcePath();
    if (!path) return null;
    const document = await decompilerClient.readResource(
      this.archive.sessionId,
      path,
    );
    return document.dataUrl;
  }

  async thumbnail(size = 64): Promise<string | null> {
    const source = await this.load();
    return source ? ImageThumbnail.create(source, size) : null;
  }

  private resourcePath(): string | null {
    const reference = this.archive.overview?.applicationIcon;
    if (!reference) return null;
    const exact = this.archive.resources.find((entry) => entry.path === reference);
    if (exact) return exact.path;
    return (
      new AndroidProjectIndex(this.archive).resource(
        reference,
        "AndroidManifest.xml",
      )?.path ?? null
    );
  }
}

class ImageThumbnail {
  static async create(source: string, size: number): Promise<string | null> {
    try {
      const image = new Image();
      image.src = source;
      await image.decode();
      if (!image.naturalWidth || !image.naturalHeight) return null;

      const canvas = document.createElement("canvas");
      canvas.width = size;
      canvas.height = size;
      const context = canvas.getContext("2d");
      if (!context) return null;

      const scale = Math.min(
        size / image.naturalWidth,
        size / image.naturalHeight,
      );
      const width = image.naturalWidth * scale;
      const height = image.naturalHeight * scale;
      context.drawImage(
        image,
        (size - width) / 2,
        (size - height) / 2,
        width,
        height,
      );
      return canvas.toDataURL("image/webp", 0.9);
    } catch {
      return null;
    }
  }
}
